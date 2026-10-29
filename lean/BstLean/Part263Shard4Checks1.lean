import BstLean.Part263Shard4Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12325_20 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83384609530137 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300633123141 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨20, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83384609530137 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300633123141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_21 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83350007070703 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300637103283 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨21, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83350007070703 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300637103283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_22 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41657714508739 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300641075281 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨22, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41657714508739 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300641075281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_23 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20820218834311 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150322550933 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨23, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20820218834311 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150322550933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_24 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16649269199391 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150324535311 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨24, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16649269199391 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150324535311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_25 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16642368192747 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287581637767 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨25, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16642368192747 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287581637767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_26 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83177360204877 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (92026283337 / 4000000000000 : ℝ))
      (E := (cell12325 ⟨26, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83177360204877 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (92026283337 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_27 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41571451843921 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150330538147 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨27, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41571451843921 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150330538147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_28 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41554235690129 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300665083981 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨28, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41554235690129 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300665083981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_29 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83074063249921 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300669051037 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨29, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83074063249921 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300669051037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_30 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20759919816197 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300673038639 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨30, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20759919816197 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300673038639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_31 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16601063878597 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575169262331 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨31, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16601063878597 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575169262331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_32 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41485491801399 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300681026879 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨32, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41485491801399 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300681026879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_33 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20734167965669 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150342515929 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨33, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20734167965669 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150342515929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_34 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20725596035307 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300689007543 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨34, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20725596035307 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300689007543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_35 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10358515050903 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575173253519 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨35, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10358515050903 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575173253519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_36 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41416940314797 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300697052853 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨36, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41416940314797 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300697052853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_37 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (3311986591097 / 4000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300701007763 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨37, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (3311986591097 / 4000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300701007763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_38 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82765472819961 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460140999387 / 20000000000000 : ℝ))
      (E := (cell12325 ⟨38, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82765472819961 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460140999387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_39 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82731304726603 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (71897156909 / 3125000000000 : ℝ))
      (E := (cell12325 ⟨39, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82731304726603 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (71897156909 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12326_20 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (3335384003261 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150245893717 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨20, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (3335384003261 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150245893717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_21 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83349997947993 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460099156637 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨21, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83349997947993 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460099156637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_22 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41657710110107 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230049977157 / 10000000000000 : ℝ))
      (E := (cell12326 ⟨22, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41657710110107 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230049977157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_23 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83280866864971 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150251907659 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨23, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83280866864971 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150251907659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_24 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (4162316892461 / 5000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300507802013 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨24, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (4162316892461 / 5000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300507802013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_25 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20802958285021 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460102358777 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨25, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20802958285021 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460102358777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_26 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83177352704857 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300515794641 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨26, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83177352704857 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300515794641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_27 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41571448255501 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150259874673 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨27, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41571448255501 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150259874673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_28 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20777116131537 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150261889011 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨28, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20777116131537 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150261889011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_29 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83074056718091 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300527766839 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨29, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83074056718091 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300527766839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_30 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83039673054789 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300531776973 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨30, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83039673054789 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300531776973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_31 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (8300531350437 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150267876231 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨31, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (8300531350437 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150267876231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_32 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82970978035119 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150269877033 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨32, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82970978035119 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150269877033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_33 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41468333307743 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300543725319 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨33, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41468333307743 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300543725319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_34 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82902379214083 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460109545313 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨34, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82902379214083 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460109545313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_35 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (129481430937 / 156250000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150275879713 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨35, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (129481430937 / 156250000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150275879713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_36 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82833876341207 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150277854033 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨36, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82833876341207 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150277854033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_37 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82799660807751 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230055974943 / 10000000000000 : ℝ))
      (E := (cell12326 ⟨37, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82799660807751 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230055974943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_38 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82765469168559 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300563708541 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨38, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82765469168559 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300563708541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_39 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82731301393031 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (46011354067 / 2000000000000 : ℝ))
      (E := (cell12326 ⟨39, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82731301393031 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (46011354067 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12327_20 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83384590634693 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (92014022553 / 4000000000000 : ℝ))
      (E := (cell12327 ⟨20, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83384590634693 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (92014022553 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_21 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83349988827023 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287544321909 / 12500000000000 : ℝ))
      (E := (cell12327 ⟨21, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83349988827023 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287544321909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_22 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83315411424649 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300358580133 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨22, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83315411424649 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300358580133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_23 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41640429197179 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150181291411 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨23, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41640429197179 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150181291411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_24 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83246329703103 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150183293761 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨24, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83246329703103 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150183293761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_25 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (8321182531801 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150185269909 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨25, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (8321182531801 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150185269909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_26 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41588672603187 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460074912021 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨26, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41588672603187 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460074912021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_27 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83142889335659 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460075707023 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨27, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83142889335659 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460075707023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_28 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41554228836747 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300382526441 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨28, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41554228836747 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300382526441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_29 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (20768512546919 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460077307417 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨29, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (20768512546919 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460077307417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_30 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41519833423083 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300390511341 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨30, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41519833423083 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300390511341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_31 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (8300530761709 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150197255087 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨31, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (8300530761709 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150197255087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_32 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (16594194493747 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575099633973 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨32, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (16594194493747 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575099633973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_33 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (5183541335597 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150201266013 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨33, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (5183541335597 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150201266013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_34 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41451187144077 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300406500353 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨34, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41451187144077 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300406500353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_35 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82868111193311 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287551312627 / 12500000000000 : ℝ))
      (E := (cell12327 ⟨35, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82868111193311 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287551312627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_36 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41416936026977 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (143775908463 / 6250000000000 : ℝ))
      (E := (cell12327 ⟨36, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41416936026977 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (143775908463 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_37 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (20699914209793 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150209243709 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨37, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (20699914209793 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150209243709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_38 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (20691366379553 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575105618793 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨38, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (20691366379553 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575105618793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_39 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (3309251922419 / 4000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300426499387 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨39, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (3309251922419 / 4000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300426499387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12328_20 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41692290594821 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460041890463 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨20, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41692290594821 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460041890463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_21 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (5209373731737 / 6250000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460042684257 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨21, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (5209373731737 / 6250000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460042684257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_22 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (650901583053 / 781250000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460043488537 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨22, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (650901583053 / 781250000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460043488537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_23 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41640424962701 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150110702191 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨23, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41640424962701 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150110702191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_24 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83246321558603 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300225427153 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨24, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83246321558603 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300225427153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_25 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83211817497513 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300229398293 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨25, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83211817497513 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300229398293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_26 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20794334427357 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300233379819 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨26, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20794334427357 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300233379819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_27 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20785720540453 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300237375199 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨27, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20785720540453 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300237375199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_28 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (10388556352787 / 12500000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575060346917 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨28, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (10388556352787 / 12500000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575060346917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_29 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41537021829339 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (92009814471 / 4000000000000 : ℝ))
      (E := (cell12328 ⟨29, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41537021829339 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (92009814471 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_30 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41519830319459 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150124679347 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨30, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41519830319459 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150124679347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_31 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (16601060346229 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300253380959 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨31, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (16601060346229 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300253380959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_32 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41485483451823 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300257372357 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨32, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41485483451823 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300257372357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_33 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82936656124873 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150130696719 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨33, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82936656124873 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150130696719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_34 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82902369363439 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (57506634687 / 2500000000000 : ℝ))
      (E := (cell12328 ⟨34, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82902369363439 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (57506634687 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_35 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20717026647029 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300269356033 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨35, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20717026647029 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300269356033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_36 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20708466941959 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300273359033 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨36, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20708466941959 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300273359033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_37 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82799652871689 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (17970916711 / 781250000000 : ℝ))
      (E := (cell12328 ⟨37, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82799652871689 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (17970916711 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_38 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82765461868921 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575070338873 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨38, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82765461868921 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575070338873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_39 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (16546258945787 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575071337629 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨39, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (16546258945787 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575071337629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12329_20 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83384571746371 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287508542053 / 12500000000000 : ℝ))
      (E := (cell12329 ⟨20, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83384571746371 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287508542053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_21 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83349970590301 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150036160611 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨21, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83349970590301 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150036160611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_22 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83315393838617 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575019089807 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨22, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83315393838617 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575019089807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_23 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (10410105182263 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575020084577 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨23, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (10410105182263 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575020084577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_24 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (2081157835393 / 2500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287510540113 / 12500000000000 : ℝ))
      (E := (cell12329 ⟨24, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (2081157835393 / 2500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287510540113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_25 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83211809678593 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460017662191 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨25, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83211809678593 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460017662191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_26 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41588665107009 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150046156083 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨26, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41588665107009 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150046156083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_27 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83142874989461 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575024082001 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨27, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83142874989461 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575024082001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_28 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41554221986277 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575025075819 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨28, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41554221986277 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575025075819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_29 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41537018565547 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300104299363 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨29, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41537018565547 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300104299363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_30 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (16607930886609 / 20000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287513539879 / 12500000000000 : ℝ))
      (E := (cell12329 ⟨30, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (16607930886609 / 20000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287513539879 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_31 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41502647923267 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (28751403829 / 1250000000000 : ℝ))
      (E := (cell12329 ⟨31, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41502647923267 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (28751403829 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_32 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82970961339851 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (35939317531 / 1562500000000 : ℝ))
      (E := (cell12329 ⟨32, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82970961339851 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (35939317531 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_33 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (10367081360181 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460024061911 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨33, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (10367081360181 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460024061911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_34 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82902364439939 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300124270807 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨34, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82902364439939 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300124270807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_35 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82868101984097 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300128265881 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨35, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82868101984097 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300128265881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_36 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41416931741427 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230013229617 / 10000000000000 : ℝ))
      (E := (cell12329 ⟨36, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41416931741427 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230013229617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_37 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (827996489053 / 1000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300136245561 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨37, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (827996489053 / 1000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300136245561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_38 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (20691364555171 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (57503507271 / 2500000000000 : ℝ))
      (E := (cell12329 ⟨38, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (20691364555171 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (57503507271 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_39 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (8273129139841 / 10000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460028851347 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨39, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (8273129139841 / 10000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460028851347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12330_20 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83384562304879 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (574981833159 / 25000000000000 : ℝ))
      (E := (cell12330 ⟨20, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83384562304879 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (574981833159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_21 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (20837490368637 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287491416669 / 12500000000000 : ℝ))
      (E := (cell12330 ⟨21, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (20837490368637 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287491416669 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_22 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83315385048147 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (459987065953 / 20000000000000 : ℝ))
      (E := (cell12330 ⟨22, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83315385048147 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (459987065953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_23 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83280832992463 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149969663147 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨23, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83280832992463 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149969663147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_24 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41623152637227 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299943327113 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨24, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41623152637227 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299943327113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_25 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83211801861249 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299947336163 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨25, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83211801861249 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299947336163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_26 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (5198582670009 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149975649383 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨26, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (5198582670009 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149975649383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_27 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (16628573563721 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299955335129 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨27, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (16628573563721 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299955335129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_28 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41554218562133 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299959273269 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨28, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41554218562133 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299959273269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_29 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (3322961224197 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (11499816457 / 500000000000 : ℝ))
      (E := (cell12330 ⟨29, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (3322961224197 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (11499816457 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_30 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83039648228547 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299967275409 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨30, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83039648228547 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299967275409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_31 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41502644981629 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114998564313 / 5000000000000 : ℝ))
      (E := (cell12330 ⟨31, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41502644981629 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114998564313 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_32 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82970955777351 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299975267733 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨32, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82970955777351 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299975267733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_33 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41468322819639 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114998964019 / 5000000000000 : ℝ))
      (E := (cell12330 ⟨33, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41468322819639 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114998964019 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_34 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82902359517653 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (574995816869 / 25000000000000 : ℝ))
      (E := (cell12330 ⟨34, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82902359517653 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (574995816869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_35 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82868097381251 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299987289161 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨35, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82868097381251 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299987289161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_36 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (16566771839801 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299991288211 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨36, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (16566771839801 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299991288211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_37 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41399822470003 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299995265719 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨37, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41399822470003 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299995265719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_38 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82765454573503 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149999640609 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨38, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82765454573503 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149999640609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_39 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (827312880689 / 1000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300003276737 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨39, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (827312880689 / 1000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300003276737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12331_20 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41692276432583 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299786382711 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨20, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41692276432583 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299786382711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_21 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41674976180267 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (143736899963 / 6250000000000 : ℝ))
      (E := (cell12331 ⟨21, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41674976180267 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (143736899963 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_22 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (5207211016211 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149897206291 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨22, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (5207211016211 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149897206291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_23 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (520505153303 / 625000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (143737398021 / 6250000000000 : ℝ))
      (E := (cell12331 ⟨23, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (520505153303 / 625000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (143737398021 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_24 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (16649259426961 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459960477489 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨24, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (16649259426961 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459960477489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_25 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (2080294851137 / 2500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299806357203 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨25, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (2080294851137 / 2500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299806357203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_26 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (16635463045561 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149905199001 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨26, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (16635463045561 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149905199001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_27 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20785715162311 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574953599143 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨27, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20785715162311 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574953599143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_28 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83108430277433 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299818356073 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨28, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83108430277433 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299818356073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_29 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83074024080171 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459964467577 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨29, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83074024080171 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459964467577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_30 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41519821012711 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (91993053791 / 4000000000000 : ℝ))
      (E := (cell12331 ⟨30, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41519821012711 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (91993053791 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_31 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20751321020329 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299830320777 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨31, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20751321020329 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299830320777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_32 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (5185684388509 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299834326647 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨32, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (5185684388509 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299834326647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_33 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82936640398361 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299838364457 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨33, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82936640398361 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299838364457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_34 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82902354596581 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574960579729 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨34, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82902354596581 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574960579729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_35 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (4143404638979 / 5000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574961577171 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨35, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (4143404638979 / 5000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574961577171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_36 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82833854916291 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299850335151 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨36, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82833854916291 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299850335151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_37 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41399820487903 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299854340843 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨37, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41399820487903 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299854340843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_38 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (5172840682961 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149929163313 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨38, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (5172840682961 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149929163313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_39 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (16546256948081 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459972458629 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨39, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (16546256948081 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459972458629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12332_20 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (2605766982101 / 3125000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574911386223 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨20, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (2605766982101 / 3125000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574911386223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_21 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83349943248257 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299649519397 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨21, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83349943248257 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299649519397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_22 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83315367472301 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459930709879 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨22, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83315367472301 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459930709879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_23 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (10410102008269 / 12500000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (35932148793 / 1562500000000 : ℝ))
      (E := (cell12332 ⟨23, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (10410102008269 / 12500000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (35932148793 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_24 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83246288996771 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459932300381 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨24, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83246288996771 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459932300381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_25 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83211786231287 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287458186349 / 12500000000000 : ℝ))
      (E := (cell12332 ⟨25, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83211786231287 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287458186349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_26 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83177307737 / 100000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149834746557 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨26, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83177307737 / 100000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149834746557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_27 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41571426740689 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299673512337 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨27, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41571426740689 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299673512337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_28 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41554211716027 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143729843329 / 6250000000000 : ℝ))
      (E := (cell12332 ⟨28, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41554211716027 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143729843329 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_29 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (8307401755683 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (91987259891 / 4000000000000 : ℝ))
      (E := (cell12332 ⟨29, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (8307401755683 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (91987259891 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_30 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83039635823671 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149842734329 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨30, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83039635823671 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149842734329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_31 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83005278200707 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (18397515747 / 800000000000 : ℝ))
      (E := (cell12332 ⟨31, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83005278200707 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (18397515747 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_32 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82970944656231 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287461687341 / 12500000000000 : ℝ))
      (E := (cell12332 ⟨32, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82970944656231 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287461687341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_33 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41468317579349 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149848751623 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨33, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41468317579349 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149848751623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_34 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82902349676723 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299701483701 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨34, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82902349676723 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299701483701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_35 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41434044089541 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299705441639 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨35, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41434044089541 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299705441639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_36 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (8283385063471 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574927359249 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨36, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (8283385063471 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574927359249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_37 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (827996370127 / 1000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459942694187 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨37, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (827996370127 / 1000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459942694187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_38 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82765447282303 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149858713533 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨38, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82765447282303 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149858713533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_39 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (3309251256517 / 4000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299721423337 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨39, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (3309251256517 / 4000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299721423337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12333_20 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20846133497769 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149752380469 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨20, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20846133497769 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149752380469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_21 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83349934137717 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299508751579 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨21, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83349934137717 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299508751579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_22 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83315358686923 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459902548041 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨22, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83315358686923 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459902548041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_23 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83280807605481 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (574879182807 / 25000000000000 : ℝ))
      (E := (cell12333 ⟨23, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83280807605481 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (574879182807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_24 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83246280860353 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287440091103 / 12500000000000 : ℝ))
      (E := (cell12333 ⟨24, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83246280860353 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287440091103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_25 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83211778418669 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299524736929 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨25, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83211778418669 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299524736929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_26 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83177300247731 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149764350431 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨26, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83177300247731 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149764350431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_27 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (16628569263001 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287441585303 / 12500000000000 : ℝ))
      (E := (cell12333 ⟨27, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (16628569263001 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287441585303 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_28 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83108416588129 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299536684841 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨28, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83108416588129 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299536684841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_29 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83074011034903 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149770355557 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨29, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83074011034903 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149770355557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_30 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41519814811647 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (229954470553 / 10000000000000 : ℝ))
      (E := (cell12333 ⟨30, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41519814811647 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (229954470553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_31 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (10375659040179 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287443583819 / 12500000000000 : ℝ))
      (E := (cell12333 ⟨31, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (10375659040179 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287443583819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_32 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82970939097611 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299552666933 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨32, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82970939097611 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299552666933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_33 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (2591769685009 / 3125000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299556696743 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨33, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (2591769685009 / 3125000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299556696743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_34 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82902344758077 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299560644691 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨34, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82902344758077 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299560644691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_35 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82868083579757 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299564688027 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨35, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82868083579757 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299564688027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_36 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82833846354263 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (57489216309 / 2500000000000 : ℝ))
      (E := (cell12333 ⟨36, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82833846354263 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (57489216309 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_37 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (1293744266417 / 1562500000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149786327997 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨37, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (1293744266417 / 1562500000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149786327997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_38 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20691360909571 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149788320601 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨38, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20691360909571 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149788320601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_39 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82731278086459 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299580667311 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨39, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82731278086459 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299580667311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12334_20 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83384524556697 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299364030853 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨20, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83384524556697 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299364030853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_21 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16669985005783 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287420997429 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨21, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16669985005783 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287420997429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_22 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83315349903241 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299371985013 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨22, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83315349903241 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299371985013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_23 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16656159829293 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299375993769 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨23, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16656159829293 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299375993769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_24 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83246272725549 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149690004937 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨24, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83246272725549 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149690004937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_25 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41605885303813 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287422997363 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨25, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41605885303813 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287422997363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_26 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16635458551999 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299387962871 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨26, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16635458551999 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299387962871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_27 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83142839150127 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299391965239 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨27, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83142839150127 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299391965239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_28 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83108409745657 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299395989237 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨28, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83108409745657 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299395989237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_29 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83074004514389 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299399979409 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨29, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83074004514389 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299399979409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_30 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83039623424289 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (143712746153 / 6250000000000 : ℝ))
      (E := (cell12334 ⟨30, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83039623424289 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (143712746153 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_31 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83005266443489 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299407985813 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨31, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83005266443489 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299407985813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_32 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (20742733385071 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574852987077 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨32, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (20742733385071 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574852987077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_33 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (8293662468313 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459883188991 / 20000000000000 : ℝ))
      (E := (cell12334 ⟨33, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (8293662468313 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459883188991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_34 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16580467968129 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299419919027 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨34, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16580467968129 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299419919027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_35 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16573615796321 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299423930663 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨35, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16573615796321 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299423930663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_36 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82833842074949 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299427922631 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨36, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82833842074949 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299427922631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_37 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82799629089769 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459886390933 / 20000000000000 : ℝ))
      (E := (cell12334 ⟨37, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82799629089769 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459886390933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_38 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82765439995319 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574858977593 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨38, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82765439995319 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574858977593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_39 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41365637380503 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994399077 / 1000000000000 : ℝ))
      (E := (cell12334 ⟨39, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41365637380503 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994399077 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12335_20 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16676903024819 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299223354637 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨20, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16676903024819 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299223354637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_21 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83349915921849 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299227377747 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨21, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83349915921849 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299227377747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_22 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16663068224251 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299231342109 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨22, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16663068224251 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299231342109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_23 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16656158137821 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149617684343 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨23, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16656158137821 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149617684343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_24 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83246264592361 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299239345053 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨24, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83246264592361 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299239345053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_25 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20802940699539 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287405416679 / 12500000000000 : ℝ))
      (E := (cell12335 ⟨25, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20802940699539 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287405416679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_26 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83177285273793 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149623668761 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨26, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83177285273793 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149623668761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_27 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41571415993371 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (114962565119 / 5000000000000 : ℝ))
      (E := (cell12335 ⟨27, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41571415993371 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (114962565119 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_28 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83108402904639 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149627644797 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨28, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83108402904639 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149627644797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_29 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (10384249749411 / 12500000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149629651079 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨29, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (10384249749411 / 12500000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149629651079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_30 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83039617226657 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299263284361 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨30, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83039617226657 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299263284361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_31 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83005260566879 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299267297159 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨31, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83005260566879 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299267297159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_32 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (331883711937 / 400000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574817821083 / 25000000000000 : ℝ))
      (E := (cell12335 ⟨32, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (331883711937 / 400000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574817821083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_33 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (3317464777889 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149637653213 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨33, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (3317464777889 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149637653213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_34 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (3316093396977 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287409913339 / 12500000000000 : ℝ))
      (E := (cell12335 ⟨34, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (3316093396977 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287409913339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_35 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41434037192313 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459856657347 / 20000000000000 : ℝ))
      (E := (cell12335 ⟨35, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41434037192313 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459856657347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_36 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82833837796767 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149643653213 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨36, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82833837796767 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149643653213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_37 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82799625129943 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299291308307 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨37, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82799625129943 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299291308307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_38 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82765436353407 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299295293243 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨38, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82765436353407 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299295293243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_39 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (10341408929571 / 12500000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149649630937 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨39, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (10341408929571 / 12500000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149649630937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12336_20 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (8338450569327 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299082790533 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨20, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (8338450569327 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299082790533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_21 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41674953408259 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459817354347 / 20000000000000 : ℝ))
      (E := (cell12336 ⟨21, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41674953408259 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459817354347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_22 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (20828833085241 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149545376603 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨22, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (20828833085241 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149545376603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_23 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83280782233399 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299094739359 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨23, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83280782233399 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299094739359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_24 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41623128230393 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459819746873 / 20000000000000 : ℝ))
      (E := (cell12336 ⟨24, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41623128230393 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459819746873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_25 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83211754990261 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574775685539 / 25000000000000 : ℝ))
      (E := (cell12336 ⟨25, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83211754990261 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574775685539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_26 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (665418222313 / 800000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299106766433 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨26, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (665418222313 / 800000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299106766433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_27 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83142824824849 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299110752253 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨27, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83142824824849 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299110752253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_28 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83108396065073 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229911470277 / 10000000000000 : ℝ))
      (E := (cell12336 ⟨28, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83108396065073 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229911470277 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_29 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83073991477599 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287389842227 / 12500000000000 : ℝ))
      (E := (cell12336 ⟨29, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83073991477599 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287389842227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_30 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83039611030397 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229912274327 / 10000000000000 : ℝ))
      (E := (cell12336 ⟨30, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83039611030397 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229912274327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_31 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83005254691601 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229912672159 / 10000000000000 : ℝ))
      (E := (cell12336 ⟨31, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83005254691601 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229912672159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_32 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82970922429507 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229913073353 / 10000000000000 : ℝ))
      (E := (cell12336 ⟨32, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82970922429507 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (229913073353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_33 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (20734153553143 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574783680653 / 25000000000000 : ℝ))
      (E := (cell12336 ⟨33, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (20734153553143 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574783680653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_34 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82902330009417 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299138690607 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨34, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82902330009417 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299138690607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_35 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82868069788819 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299142697651 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨35, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82868069788819 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299142697651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_36 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41416916759859 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299146686513 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨36, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41416916759859 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299146686513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_37 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (8279962117121 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149575358461 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨37, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (8279962117121 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149575358461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_38 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (20691358178137 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149577336243 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨38, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (20691358178137 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149577336243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_39 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82731268113143 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299158671149 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨39, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82731268113143 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299158671149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12337_20 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83384496264221 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (22989422803 / 1000000000000 : ℝ))
      (E := (cell12337 ⟨20, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83384496264221 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (22989422803 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_21 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (20837474428231 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149473138961 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨21, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (20837474428231 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149473138961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_22 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (650900965331 / 781250000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459790043661 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨22, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (650900965331 / 781250000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459790043661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_23 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83280773779347 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229895422241 / 10000000000000 : ℝ))
      (E := (cell12337 ⟨23, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83280773779347 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229895422241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_24 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (3329849933233 / 4000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298958236143 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨24, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (3329849933233 / 4000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298958236143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_25 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41605873591969 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298962205079 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨25, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41605873591969 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298962205079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_26 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83177270305989 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (287370781201 / 12500000000000 : ℝ))
      (E := (cell12337 ⟨26, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83177270305989 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (287370781201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_27 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83142817664449 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71842818689 / 3125000000000 : ℝ))
      (E := (cell12337 ⟨27, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83142817664449 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71842818689 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_28 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83108389226959 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71842944649 / 3125000000000 : ℝ))
      (E := (cell12337 ⟨28, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83108389226959 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71842944649 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_29 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41536992480661 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298978227931 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨29, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41536992480661 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298978227931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_30 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (8303960483551 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (143686387389 / 6250000000000 : ℝ))
      (E := (cell12337 ⟨30, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (8303960483551 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (143686387389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_31 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (16601049763531 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71843318769 / 3125000000000 : ℝ))
      (E := (cell12337 ⟨31, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (16601049763531 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (71843318769 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_32 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (10371364609507 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (287373772357 / 12500000000000 : ℝ))
      (E := (cell12337 ⟨32, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (10371364609507 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (287373772357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_33 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82936608979171 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149497096757 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨33, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82936608979171 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149497096757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_34 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (4145116254781 / 5000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574749546963 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨34, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (4145116254781 / 5000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574749546963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_35 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (10358508149273 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299002163411 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨35, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (10358508149273 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299002163411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_36 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82833829243801 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (18392049441 / 800000000000 : ℝ))
      (E := (cell12337 ⟨36, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82833829243801 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (18392049441 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_37 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82799617213569 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229901018051 / 10000000000000 : ℝ))
      (E := (cell12337 ⟨37, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82799617213569 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229901018051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_38 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41382714536371 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299014165431 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨38, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41382714536371 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299014165431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_39 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (8273126479073 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459803638843 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨39, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (8273126479073 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459803638843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12338_20 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20846121709237 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298801823941 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨20, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20846121709237 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298801823941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_21 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (10418736076383 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149402889893 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨21, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (10418736076383 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149402889893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_22 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41657657392733 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298809795697 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨22, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41657657392733 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298809795697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_23 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83280765326949 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149406908921 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨23, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83280765326949 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149406908921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_24 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41623120101239 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287352224007 / 12500000000000 : ℝ))
      (E := (cell12338 ⟨24, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41623120101239 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287352224007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_25 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20802934844797 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298821780559 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨25, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20802934844797 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298821780559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_26 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16635452564877 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287353223381 / 12500000000000 : ℝ))
      (E := (cell12338 ⟨26, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16635452564877 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287353223381 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_27 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83142810505541 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149414878289 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨27, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83142810505541 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149414878289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_28 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83108382390297 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574708437683 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨28, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83108382390297 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574708437683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_29 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83073978446457 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459767554501 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨29, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83073978446457 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459767554501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_30 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83039598641993 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (114942088309 / 5000000000000 : ℝ))
      (E := (cell12338 ⟨30, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83039598641993 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (114942088309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_31 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (1037565536813 / 1250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149422867107 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨31, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (1037565536813 / 1250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149422867107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_32 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (10371363915487 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149424868679 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨32, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (10371363915487 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149424868679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_33 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82936603747021 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (28735672221 / 1250000000000 : ℝ))
      (E := (cell12338 ⟨33, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82936603747021 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (28735672221 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_34 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16580464036607 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298857739879 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨34, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16580464036607 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298857739879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_35 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (1035850757509 / 1250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298861742613 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨35, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (1035850757509 / 1250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298861742613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_36 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (10354228121127 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287358216081 / 12500000000000 : ℝ))
      (E := (cell12338 ⟨36, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (10354228121127 / 12500000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (287358216081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_37 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (4139980662851 / 5000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149434878857 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨37, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (4139980662851 / 5000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149434878857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_38 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20691356358497 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459774742683 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨38, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20691356358497 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459774742683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_39 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82731261469331 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (71839928553 / 3125000000000 : ℝ))
      (E := (cell12338 ⟨39, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82731261469331 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (71839928553 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12339_20 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83384477411451 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298661421457 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨20, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83384477411451 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298661421457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_21 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83349879510939 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149332726059 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨21, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83349879510939 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149332726059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_22 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41657653005129 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459733885419 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨22, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41657653005129 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459733885419 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_23 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20820189219051 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149336704517 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨23, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20820189219051 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149336704517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_24 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83246232075743 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459735480421 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨24, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83246232075743 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459735480421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_25 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83211731576011 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (7183379407 / 312500000000 : ℝ))
      (E := (cell12339 ⟨25, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83211731576011 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (7183379407 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_26 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41588627672157 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298685378753 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨26, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41588627672157 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298685378753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_27 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (133028485357 / 160000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574672356961 / 25000000000000 : ℝ))
      (E := (cell12339 ⟨27, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (133028485357 / 160000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574672356961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_28 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41554187777543 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298693385521 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨28, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41554187777543 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298693385521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_29 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83073971933003 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298697371539 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨29, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83073971933003 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298697371539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_30 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (10379949056231 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298701388659 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨30, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (10379949056231 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298701388659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_31 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20751309268439 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229870538091 / 10000000000000 : ℝ))
      (E := (cell12339 ⟨31, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20751309268439 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229870538091 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_32 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82970905773027 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459741870103 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨32, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82970905773027 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459741870103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_33 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41468299258061 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149356679009 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨33, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41468299258061 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149356679009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_34 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82902315271661 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229871734669 / 10000000000000 : ℝ))
      (E := (cell12339 ⟨34, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82902315271661 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229871734669 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_35 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20717014002107 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298721376661 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨35, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20717014002107 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298721376661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_36 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41416910347681 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298725390701 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨36, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41416910347681 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298725390701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_37 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82799609301563 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149364665627 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨37, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82799609301563 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149364665627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_38 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41382710898143 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459746675021 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨38, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41382710898143 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459746675021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_39 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (5170703634309 / 6250000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229873734697 / 10000000000000 : ℝ))
      (E := (cell12339 ⟨39, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (5170703634309 / 6250000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229873734697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12340_20 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (5211529249233 / 6250000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298521131091 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨20, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (5211529249233 / 6250000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298521131091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_21 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20837467603137 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (17957227501 / 781250000000 : ℝ))
      (E := (cell12340 ⟨21, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20837467603137 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (17957227501 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_22 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (10414412154593 / 12500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298529112499 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨22, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (10414412154593 / 12500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298529112499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_23 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83280748427113 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (71829159769 / 3125000000000 : ℝ))
      (E := (cell12340 ⟨23, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83280748427113 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (71829159769 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_24 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83246223950621 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149268562313 / 50000000000000 : ℝ))
      (E := (cell12340 ⟨24, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83246223950621 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149268562313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_25 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41605861887203 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574635273531 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨25, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41605861887203 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574635273531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_26 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41588623932887 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574636270777 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨26, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41588623932887 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574636270777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_27 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (415713980961 / 500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298549095037 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨27, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (415713980961 / 500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298549095037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_28 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41554184360663 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298553074707 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨28, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41554184360663 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298553074707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_29 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (519212283881 / 625000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298557083489 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨29, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (519212283881 / 625000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298557083489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_30 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83039586259073 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298561065667 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨30, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83039586259073 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298561065667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_31 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83005231203803 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574641270549 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨31, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83005231203803 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574641270549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_32 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82970900223449 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (45971381537 / 2000000000000 : ℝ))
      (E := (cell12340 ⟨32, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82970900223449 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (45971381537 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_33 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41468296643237 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287321631453 / 12500000000000 : ℝ))
      (E := (cell12340 ⟨33, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41468296643237 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287321631453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_34 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41451155180749 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287322133357 / 12500000000000 : ℝ))
      (E := (cell12340 ⟨34, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41451155180749 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287322133357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_35 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41434025708653 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (57464526639 / 2500000000000 : ℝ))
      (E := (cell12340 ⟨35, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41434025708653 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (57464526639 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_36 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82833816422839 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298585049051 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨36, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82833816422839 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298585049051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_37 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82799605347197 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298589077053 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨37, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82799605347197 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298589077053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_38 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (16553083631927 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149296516587 / 50000000000000 : ℝ))
      (E := (cell12340 ⟨38, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (16553083631927 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149296516587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_39 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (161584482089 / 195312500000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287324629419 / 12500000000000 : ℝ))
      (E := (cell12340 ⟨39, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (161584482089 / 195312500000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287324629419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12341_20 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83384458565779 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298380894603 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨20, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83384458565779 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298380894603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_21 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (8334986131589 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298384900347 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨21, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (8334986131589 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298384900347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_22 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83315288464923 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287298606489 / 12500000000000 : ℝ))
      (E := (cell12341 ⟨22, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83315288464923 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287298606489 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_23 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41640369989837 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298392870257 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨23, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41640369989837 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298392870257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_24 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83246215827111 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298396842951 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨24, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83246215827111 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298396842951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_25 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (20802928993593 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229840089057 / 10000000000000 : ℝ))
      (E := (cell12341 ⟨25, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (20802928993593 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229840089057 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_26 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41588620194383 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298404841731 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨26, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41588620194383 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298404841731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_27 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41571394518883 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229840887497 / 10000000000000 : ℝ))
      (E := (cell12341 ⟨27, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41571394518883 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229840887497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_28 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83108361889017 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28730160959 / 1250000000000 : ℝ))
      (E := (cell12341 ⟨28, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83108361889017 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28730160959 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_29 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83073958910327 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298416849901 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨29, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83073958910327 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298416849901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_30 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (20759895017417 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149210427839 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨30, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (20759895017417 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149210427839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_31 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (4150261266759 / 5000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574606209519 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨31, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (4150261266759 / 5000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574606209519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_32 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82970894675161 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298428857843 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨32, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82970894675161 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298428857843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_33 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (3317463522323 / 4000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149216429249 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨33, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (3317463522323 / 4000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149216429249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_34 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41451152726273 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298436841807 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨34, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41451152726273 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298436841807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_35 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16573609365471 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298440809309 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨35, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16573609365471 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298440809309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_36 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82833812151447 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574611205233 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨36, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82833812151447 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574611205233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_37 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41399800696961 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287306102399 / 12500000000000 : ℝ))
      (E := (cell12341 ⟨37, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41399800696961 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287306102399 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_38 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (20691353631009 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298452804949 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨38, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (20691353631009 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298452804949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_39 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16546250302241 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298456837527 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨39, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16546250302241 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298456837527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12342_20 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20846112286401 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459648142399 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨20, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20846112286401 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459648142399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_21 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41674926110483 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298244734509 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨21, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41674926110483 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298244734509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_22 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41657639847397 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298248703623 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨22, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41657639847397 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298248703623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_23 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83280731533887 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298252681981 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨23, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83280731533887 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298252681981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_24 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20811551926303 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287282084219 / 12500000000000 : ℝ))
      (E := (cell12342 ⟨24, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20811551926303 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287282084219 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_25 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (8321170817591 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149130341431 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨25, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (8321170817591 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149130341431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_26 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (10397154114161 / 12500000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298264713007 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨26, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (10397154114161 / 12500000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298264713007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_27 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83142781884823 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298268709237 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨27, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83142781884823 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298268709237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_28 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83108355058159 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298272674703 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨28, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83108355058159 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298272674703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_29 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (5192122025069 / 6250000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149138335389 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨29, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (5192122025069 / 6250000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149138335389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_30 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41519786940817 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149140350109 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨30, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41519786940817 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149140350109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_31 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83005219467887 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298284648549 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨31, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83005219467887 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298284648549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_32 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82970889128163 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459657738699 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨32, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82970889128163 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459657738699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_33 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82936582830927 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574573165387 / 25000000000000 : ℝ))
      (E := (cell12342 ⟨33, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82936582830927 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574573165387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_34 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82902300544803 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149148335773 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨34, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82902300544803 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149148335773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_35 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (3314721689543 / 4000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298300666503 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨35, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (3314721689543 / 4000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298300666503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_36 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41416903940593 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (229830464773 / 10000000000000 : ℝ))
      (E := (cell12342 ⟨36, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41416903940593 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (229830464773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_37 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41399798720869 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298308674951 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨37, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41399798720869 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298308674951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_38 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82765410889489 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298312631769 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨38, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82765410889489 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298312631769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_39 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82731248193853 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (18386533089 / 800000000000 : ℝ))
      (E := (cell12342 ⟨39, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82731248193853 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (18386533089 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12343_20 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83384439727203 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298100641509 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨20, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83384439727203 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298100641509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_21 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (3333993725111 / 4000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298104622619 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨21, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (3333993725111 / 4000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298104622619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_22 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41657635463179 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149054304673 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨22, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41657635463179 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149054304673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_23 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83280723089751 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149056303047 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨23, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83280723089751 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149056303047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_24 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20811549896231 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229811661703 / 10000000000000 : ℝ))
      (E := (cell12343 ⟨24, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20811549896231 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229811661703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_25 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41605850189509 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298120587721 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨25, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41605850189509 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298120587721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_26 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (4158861271967 / 5000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298124580173 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨26, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (4158861271967 / 5000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298124580173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_27 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8314277473337 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (28726607473 / 1250000000000 : ℝ))
      (E := (cell12343 ⟨27, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8314277473337 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (28726607473 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_28 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (66486678583 / 80000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149066292759 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨28, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (66486678583 / 80000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149066292759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_29 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83073945893291 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (91925464183 / 4000000000000 : ℝ))
      (E := (cell12343 ⟨29, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83073945893291 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (91925464183 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_30 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83039567694969 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229814059929 / 10000000000000 : ℝ))
      (E := (cell12343 ⟨30, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83039567694969 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229814059929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_31 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83005213601923 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149072286059 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨31, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83005213601923 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149072286059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_32 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (16594176716491 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149074291903 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨32, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (16594176716491 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149074291903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_33 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82936577605029 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229815257787 / 10000000000000 : ℝ))
      (E := (cell12343 ⟨33, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82936577605029 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (229815257787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_34 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8290229563827 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (91926262243 / 4000000000000 : ℝ))
      (E := (cell12343 ⟨34, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8290229563827 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (91926262243 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_35 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20717009412741 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287270072319 / 12500000000000 : ℝ))
      (E := (cell12343 ⟨35, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20717009412741 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287270072319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_36 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41416901806027 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149082264723 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨36, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41416901806027 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149082264723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_37 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20699898372661 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574542131763 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨37, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20699898372661 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574542131763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_38 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (10345675906999 / 12500000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (22981725723 / 1000000000000 : ℝ))
      (E := (cell12343 ⟨38, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (10345675906999 / 12500000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (22981725723 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_39 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82731244877513 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (57454413713 / 2500000000000 : ℝ))
      (E := (cell12343 ⟨39, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82731244877513 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (57454413713 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12344_20 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (3335377212423 / 4000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287245070833 / 12500000000000 : ℝ))
      (E := (cell12344 ⟨20, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (3335377212423 / 4000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287245070833 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_21 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (20837458509079 / 25000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (91918582587 / 4000000000000 : ℝ))
      (E := (cell12344 ⟨21, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (20837458509079 / 25000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (91918582587 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_22 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83315262159613 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148984284541 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨22, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83315262159613 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148984284541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_23 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83280714647267 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459594516857 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨23, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83280714647267 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459594516857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_24 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (10405773933281 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148988278057 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨24, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (10405773933281 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148988278057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_25 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (5200730786481 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574495136697 / 25000000000000 : ℝ))
      (E := (cell12344 ⟨25, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (5200730786481 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574495136697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_26 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83177217966923 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297984559993 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨26, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83177217966923 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297984559993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_27 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41571383791703 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297988540783 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨27, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41571383791703 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297988540783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_28 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (8310834140079 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459598510147 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨28, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (8310834140079 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459598510147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_29 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83073939386887 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459599306877 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨29, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83073939386887 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459599306877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_30 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83039561509673 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149000276447 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨30, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83039561509673 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149000276447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_31 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (10375650967161 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574501137571 / 25000000000000 : ℝ))
      (E := (cell12344 ⟨31, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (10375650967161 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574501137571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_32 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (16594175607607 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298008528779 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨32, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (16594175607607 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298008528779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_33 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82936572380379 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149006274459 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨33, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82936572380379 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149006274459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_34 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41451145366473 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459603310793 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨34, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41451145366473 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459603310793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_35 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82868033064523 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149010272727 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨35, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82868033064523 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149010272727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_36 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82833799344053 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149012262349 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨36, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82833799344053 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149012262349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_37 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (517497434629 / 625000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298028492777 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨37, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (517497434629 / 625000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298028492777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_38 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (16553080724709 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459606501843 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨38, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (16553080724709 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459606501843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_39 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82731241562183 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574509129007 / 25000000000000 : ℝ))
      (E := (cell12344 ⟨39, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82731241562183 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574509129007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12345_20 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83384420895719 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297820603943 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨20, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83384420895719 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297820603943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_21 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20837456236647 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297824618947 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨21, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20837456236647 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297824618947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_22 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (130180083429 / 156250000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297828641119 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨22, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (130180083429 / 156250000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297828641119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_23 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83280706206433 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459566523311 / 20000000000000 : ℝ))
      (E := (cell12345 ⟨23, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83280706206433 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459566523311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_24 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83246183349181 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297836607679 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨24, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83246183349181 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297836607679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_25 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16642336957989 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297840618421 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨25, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16642336957989 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297840618421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_26 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16635442099207 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287230574261 / 12500000000000 : ℝ))
      (E := (cell12345 ⟨26, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16635442099207 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287230574261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_27 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20785690108733 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574462149117 / 25000000000000 : ℝ))
      (E := (cell12345 ⟨27, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20785690108733 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574462149117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_28 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (2077708364357 / 2500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459570514071 / 20000000000000 : ℝ))
      (E := (cell12345 ⟨28, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (2077708364357 / 2500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459570514071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_29 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83073932881893 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574464144279 / 25000000000000 : ℝ))
      (E := (cell12345 ⟨29, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83073932881893 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574464144279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_30 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41519777662873 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (229786056103 / 10000000000000 : ℝ))
      (E := (cell12345 ⟨30, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41519777662873 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (229786056103 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_31 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41502600936991 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287233072881 / 12500000000000 : ℝ))
      (E := (cell12345 ⟨31, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41502600936991 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287233072881 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_32 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (10371359061863 / 12500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148934293469 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨32, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (10371359061863 / 12500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148934293469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_33 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82936567156979 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574468143673 / 25000000000000 : ℝ))
      (E := (cell12345 ⟨33, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82936567156979 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574468143673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_34 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (2590696432151 / 3125000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148938274037 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨34, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (2590696432151 / 3125000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148938274037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_35 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (331472113917 / 400000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297880567213 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨35, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (331472113917 / 400000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297880567213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_36 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82833795077181 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297884574869 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨36, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82833795077181 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297884574869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_37 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41399792795863 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297888572127 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨37, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41399792795863 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297888572127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_38 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20691349998037 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148946279921 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨38, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20691349998037 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148946279921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_39 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (10341404780983 / 12500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297896538647 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨39, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (10341404780983 / 12500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297896538647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12346_20 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (16676882296527 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297680753351 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨20, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (16676882296527 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297680753351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_21 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (2604681745581 / 3125000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (17950661931 / 781250000000 : ℝ))
      (E := (cell12346 ⟨21, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (2604681745581 / 3125000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (17950661931 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_22 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83315244631197 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459537741777 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨22, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83315244631197 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459537741777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_23 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (333122791069 / 400000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459538540581 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨23, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (333122791069 / 400000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459538540581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_24 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20811543808431 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297696713391 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨24, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20811543808431 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297696713391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_25 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83211676997763 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297700685907 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨25, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83211676997763 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297700685907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_26 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20794300756669 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297704682459 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨26, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20794300756669 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297704682459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_27 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41571376643973 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297708706497 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨27, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41571376643973 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297708706497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_28 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41554163874609 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574428175703 / 25000000000000 : ℝ))
      (E := (cell12346 ⟨28, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41554163874609 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574428175703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_29 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41536963189153 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297716674319 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨29, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41536963189153 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297716674319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_30 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20759887285797 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148860341089 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨30, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20759887285797 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148860341089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_31 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (16601039202401 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (229772467041 / 10000000000000 : ℝ))
      (E := (cell12346 ⟨31, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (16601039202401 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (229772467041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_32 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41485433476531 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297728699761 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨32, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41485433476531 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297728699761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_33 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82936561934827 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459546531039 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨33, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82936561934827 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459546531039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_34 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41451140462963 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297736655547 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨34, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41451140462963 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297736655547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_35 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82868023895147 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297740702423 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨35, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82868023895147 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297740702423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_36 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41416895405719 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297744679963 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨36, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41416895405719 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297744679963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_37 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41399790821951 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148874323911 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨37, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41399790821951 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148874323911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_38 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41382698180901 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297752665519 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨38, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41382698180901 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297752665519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_39 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (16546246986911 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (229775667507 / 10000000000000 : ℝ))
      (E := (cell12346 ⟨39, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (16546246986911 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (229775667507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12347_20 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83384402071323 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297540898403 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨20, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83384402071323 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297540898403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_21 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (10418725846541 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114877244467 / 5000000000000 : ℝ))
      (E := (cell12347 ⟨21, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (10418725846541 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114877244467 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_22 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (3332609434781 / 4000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574387222239 / 25000000000000 : ℝ))
      (E := (cell12347 ⟨22, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (3332609434781 / 4000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574387222239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_23 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83280689329717 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297552901649 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨23, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83280689329717 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297552901649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_24 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83246167119877 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71798652289 / 3125000000000 : ℝ))
      (E := (cell12347 ⟨24, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83246167119877 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71798652289 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_25 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83211669207149 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459512173193 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨25, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83211669207149 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459512173193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_26 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (41588597779423 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71798902609 / 3125000000000 : ℝ))
      (E := (cell12347 ⟨26, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (41588597779423 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71798902609 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_27 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83142746142449 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459513774173 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨27, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83142746142449 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459513774173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_28 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16621664185121 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148786444837 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨28, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16621664185121 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148786444837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_29 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (2596059996129 / 3125000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459515376889 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨29, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (2596059996129 / 3125000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459515376889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_30 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83039542961997 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148790428931 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨30, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83039542961997 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148790428931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_31 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16601038030271 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148792435437 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨31, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16601038030271 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148792435437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_32 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (20742715353127 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (143599304203 / 6250000000000 : ℝ))
      (E := (cell12347 ⟨32, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (20742715353127 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (143599304203 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_33 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82936556713923 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148796424487 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨33, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82936556713923 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148796424487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_34 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (20725569006057 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459519375277 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨34, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (20725569006057 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459519375277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_35 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (20717004828053 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297600833897 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨35, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (20717004828053 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297600833897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_36 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82833786546823 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114880241999 / 5000000000000 : ℝ))
      (E := (cell12347 ⟨36, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82833786546823 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114880241999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_37 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82799577697167 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (287201104643 / 12500000000000 : ℝ))
      (E := (cell12347 ⟨37, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82799577697167 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (287201104643 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_38 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16553078546501 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148806413123 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨38, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16553078546501 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148806413123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_39 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (5170701976391 / 6250000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297616807919 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨39, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (5170701976391 / 6250000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297616807919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12348_20 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41692196330891 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459480231117 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨20, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41692196330891 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459480231117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_21 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83349797687793 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297405163733 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨21, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83349797687793 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297405163733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_22 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83315227109543 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459481824609 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨22, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83315227109543 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459481824609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_23 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83280680893833 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148706577239 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨23, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83280680893833 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148706577239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_24 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83246159007639 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (229741714559 / 10000000000000 : ℝ))
      (E := (cell12348 ⟨24, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83246159007639 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (229741714559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_25 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (16642332283621 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459484231719 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨25, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (16642332283621 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459484231719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_26 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (16635437618509 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297425138797 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨26, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (16635437618509 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297425138797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_27 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (2078568474961 / 2500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143589321749 / 6250000000000 : ℝ))
      (E := (cell12348 ⟨27, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (2078568474961 / 2500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143589321749 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_28 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83108314103439 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459486626189 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨28, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83108314103439 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459486626189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_29 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41536956687679 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297437090591 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨29, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41536956687679 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297437090591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_30 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41519768391087 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297441088083 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨30, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41519768391087 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297441088083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_31 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41502592146017 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297445125939 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨31, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41502592146017 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297445125939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_32 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82970855873241 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297449089403 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨32, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82970855873241 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297449089403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_33 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82936551494267 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574363274371 / 25000000000000 : ℝ))
      (E := (cell12348 ⟨33, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82936551494267 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574363274371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_34 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41451135561869 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287182136681 / 12500000000000 : ℝ))
      (E := (cell12348 ⟨34, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41451135561869 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287182136681 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_35 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41434007365223 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287182634853 / 12500000000000 : ℝ))
      (E := (cell12348 ⟨35, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41434007365223 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287182634853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_36 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41416891141669 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297465113537 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨36, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41416891141669 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297465113537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_37 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (517497335947 / 625000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143591817591 / 6250000000000 : ℝ))
      (E := (cell12348 ⟨37, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (517497335947 / 625000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143591817591 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_38 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82765389104257 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574368275173 / 25000000000000 : ℝ))
      (E := (cell12348 ⟨38, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82765389104257 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574368275173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_39 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82731228310967 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297477054573 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨39, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82731228310967 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297477054573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12349_20 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83384383254011 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297261466657 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨20, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83384383254011 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297261466657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_21 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83349788604989 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (28715818651 / 1250000000000 : ℝ))
      (E := (cell12349 ⟨21, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83349788604989 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (28715818651 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_22 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (66652174681 / 80000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574317367361 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨22, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (66652174681 / 80000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574317367361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_23 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41640336229799 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (143579591337 / 6250000000000 : ℝ))
      (E := (cell12349 ⟨23, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41640336229799 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (143579591337 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_24 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83246150897009 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297277472083 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨24, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83246150897009 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297277472083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_25 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83211653630629 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297281447081 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨25, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83211653630629 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297281447081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_26 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83177180627771 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459457089677 / 20000000000000 : ℝ))
      (E := (cell12349 ⟨26, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83177180627771 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459457089677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_27 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83142731855919 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297289421041 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨27, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83142731855919 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297289421041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_28 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83108307282721 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (18378347413 / 800000000000 : ℝ))
      (E := (cell12349 ⟨28, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83108307282721 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (18378347413 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_29 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41536953437997 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459459481933 / 20000000000000 : ℝ))
      (E := (cell12349 ⟨29, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41536953437997 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459459481933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_30 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83039530603719 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (57432535783 / 2500000000000 : ℝ))
      (E := (cell12349 ⟨30, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83039530603719 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (57432535783 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_31 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83005178434039 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287163179451 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨31, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83005178434039 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287163179451 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_32 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41485425167631 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574327356187 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨32, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41485425167631 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574327356187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_33 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41468273137929 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287164175091 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨33, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41468273137929 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287164175091 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_34 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (10362783278057 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297317423879 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨34, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (10362783278057 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297317423879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_35 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82868010149847 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148660689307 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨35, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82868010149847 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148660689307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_36 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (4141688901049 / 5000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297325383403 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨36, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (4141688901049 / 5000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297325383403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_37 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41399784903481 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297329380757 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨37, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41399784903481 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297329380757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_38 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41382692738529 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297333371527 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨38, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41382692738529 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297333371527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_39 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82731225000687 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297337415033 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨39, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82731225000687 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297337415033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

end BstLean.Part263
