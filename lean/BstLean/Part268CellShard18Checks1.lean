import BstLean.Part268CellShard18Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12800_20 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20845078500269 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (34991264323 / 1562500000000 : ℝ))
      (E := (cell12800 ⟨20, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20845078500269 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (34991264323 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_21 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83345861898119 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239444948591 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨21, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83345861898119 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239444948591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_22 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20827858497861 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (4373923663 / 195312500000 : ℝ))
      (E := (cell12800 ⟨22, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20827858497861 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (4373923663 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_23 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (1301203597629 / 1562500000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119726468753 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨23, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (1301203597629 / 1562500000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119726468753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_24 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41621325317963 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239456959791 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨24, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41621325317963 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239456959791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_25 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (16641659024399 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239460927027 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨25, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (16641659024399 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239460927027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_26 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (10396745459271 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559866239723 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨26, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (10396745459271 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559866239723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_27 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83139656260317 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239468941211 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨27, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83139656260317 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239468941211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_28 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83105372848477 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119736467407 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨28, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83105372848477 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119736467407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_29 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (648993073491 / 781250000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119738470947 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨29, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (648993073491 / 781250000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119738470947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_30 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83036877903791 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239480964417 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨30, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83036877903791 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239480964417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_31 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83002666307829 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239484945571 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨31, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83002666307829 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239484945571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_32 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20742119646911 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559872236341 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨32, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20742119646911 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559872236341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_33 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82934314712081 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (139968310317 / 6250000000000 : ℝ))
      (E := (cell12800 ⟨33, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82934314712081 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (139968310317 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_34 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41450087325069 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119748502877 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨34, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41450087325069 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119748502877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_35 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (2589564324093 / 3125000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239501009593 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨35, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (2589564324093 / 3125000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239501009593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_36 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (82831965843907 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239504977127 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨36, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (82831965843907 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239504977127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_37 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20699474259601 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559877256509 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨37, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20699474259601 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559877256509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_38 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8276385192409 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239512980419 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨38, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8276385192409 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239512980419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_39 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (10341228808843 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239517016271 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨39, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (10341228808843 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239517016271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12801_20 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16676061069761 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239321406901 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨20, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16676061069761 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239321406901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_21 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16669170710657 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119662712327 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨21, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16669170710657 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119662712327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_22 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41655712976809 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239329436393 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨22, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41655712976809 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239329436393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_23 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83277022517011 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239333445707 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨23, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83277022517011 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239333445707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_24 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16648528642167 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119668727979 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨24, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16648528642167 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119668727979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_25 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (10401036000329 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119670705931 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨25, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (10401036000329 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119670705931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_26 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (20793489215027 / 25000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239345433097 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨26, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (20793489215027 / 25000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239345433097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_27 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (2598114054723 / 3125000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (17494917687 / 781250000000 : ℝ))
      (E := (cell12801 ⟨27, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (2598114054723 / 3125000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (17494917687 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_28 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (10388170830469 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239353448329 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨28, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (10388170830469 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239353448329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_29 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (20767776876539 / 25000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119678723449 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨29, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (20767776876539 / 25000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119678723449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_30 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83036872306711 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119680730803 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨30, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83036872306711 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119680730803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_31 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83002661013939 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239365435643 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨31, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83002661013939 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239365435643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_32 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41484236798263 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119684743791 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨32, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41484236798263 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119684743791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_33 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41467155011657 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119686721497 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨33, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41467155011657 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119686721497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_34 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16580034052661 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119688739321 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨34, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16580034052661 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119688739321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_35 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41433027142829 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119690739071 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨35, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41433027142829 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119690739071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_36 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (10353995257461 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559846375173 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨36, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (10353995257461 / 12500000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559846375173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_37 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82797893554867 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239389487983 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨37, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82797893554867 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239389487983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_38 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (4138192437041 / 5000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559848374703 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨38, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (4138192437041 / 5000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559848374703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_39 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (82729827587327 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111969873719 / 5000000000000 : ℝ))
      (E := (cell12801 ⟨39, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (82729827587327 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111969873719 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12802_20 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (325704283977 / 390625000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (69975060987 / 3125000000000 : ℝ))
      (E := (cell12802 ⟨20, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (325704283977 / 390625000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (69975060987 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_21 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83345845209991 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119602977617 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨21, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83345845209991 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119602977617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_22 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16662283583459 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239209953573 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨22, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16662283583459 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239209953573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_23 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (2602406712101 / 3125000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223921395019 / 10000000000000 : ℝ))
      (E := (cell12802 ⟨23, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (2602406712101 / 3125000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223921395019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_24 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83242635787173 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447843589689 / 20000000000000 : ℝ))
      (E := (cell12802 ⟨24, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83242635787173 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447843589689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_25 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83208280884661 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239221951461 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨25, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83208280884661 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239221951461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_26 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (20793487511851 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (17913807697 / 800000000000 : ℝ))
      (E := (cell12802 ⟨26, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (20793487511851 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (17913807697 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_27 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41569821621637 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239229983093 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨27, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41569821621637 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239229983093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_28 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83105360440309 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119616979157 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨28, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83105360440309 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119616979157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_29 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (8307110160671 / 10000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239237948409 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨29, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (8307110160671 / 10000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239237948409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_30 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (2075921667771 / 2500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111962097767 / 5000000000000 : ℝ))
      (E := (cell12802 ⟨30, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (2075921667771 / 2500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111962097767 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_31 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83002655721223 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119622990421 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨31, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83002655721223 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119622990421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_32 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (5185529287909 / 6250000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (44784999357 / 2000000000000 : ℝ))
      (E := (cell12802 ⟨32, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (5185529287909 / 6250000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (44784999357 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_33 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82934305335647 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119626988083 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨33, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82934305335647 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119626988083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_34 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16580033175507 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (55981450171 / 2500000000000 : ℝ))
      (E := (cell12802 ⟨34, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16580033175507 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (55981450171 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_35 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82866050201367 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119631001031 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨35, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82866050201367 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119631001031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_36 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82831958276459 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (89570640841 / 4000000000000 : ℝ))
      (E := (cell12802 ⟨36, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82831958276459 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (89570640841 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_37 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16559578014457 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239270005421 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨37, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16559578014457 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239270005421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_38 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82763845558469 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119637007023 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨38, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82763845558469 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119637007023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_39 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (82729824704793 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119639023417 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨39, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (82729824704793 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119639023417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12803_20 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16676057609799 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119541246219 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨20, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16676057609799 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119541246219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_21 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (20836459217059 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119543241011 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨21, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (20836459217059 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119543241011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_22 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (3332456395299 / 4000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239090466997 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨22, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (3332456395299 / 4000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239090466997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_23 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41638503529459 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119547254657 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨23, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41638503529459 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119547254657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_24 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (4162131418247 / 5000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447819699127 / 20000000000000 : ℝ))
      (E := (cell12803 ⟨24, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (4162131418247 / 5000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447819699127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_25 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83208273768083 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239102487417 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨25, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83208273768083 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239102487417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_26 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16634788647211 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239106487549 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨26, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16634788647211 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239106487549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_27 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83139636736731 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559777624671 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨27, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83139636736731 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559777624671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_28 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83105354238149 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447822904649 / 20000000000000 : ℝ))
      (E := (cell12803 ⟨28, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83105354238149 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447822904649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_29 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (8307109570851 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239118504927 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨29, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (8307109570851 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239118504927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_30 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41518430558089 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119561252071 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨30, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41518430558089 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119561252071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_31 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83002650429679 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (8746587979 / 390625000000 : ℝ))
      (E := (cell12803 ⟨31, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83002650429679 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (8746587979 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_32 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41484231808849 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119565280939 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨32, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41484231808849 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119565280939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_33 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (2073357516227 / 2500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239134564587 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨33, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (2073357516227 / 2500000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239134564587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_34 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (20725040373207 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119569265867 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨34, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (20725040373207 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119569265867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_35 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82866046118103 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239142522713 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨35, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82866046118103 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239142522713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_36 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41415977247111 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239146538127 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨36, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41415977247111 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239146538127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_37 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82797886590657 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239150578353 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨37, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82797886590657 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239150578353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_38 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82763842377037 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119577292417 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨38, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82763842377037 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119577292417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_39 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (82729821823141 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559789639359 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨39, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (82729821823141 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559789639359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12804_20 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16676055880291 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238963087749 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨20, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16676055880291 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238963087749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_21 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (83345828528021 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223896706333 / 10000000000000 : ℝ))
      (E := (cell12804 ⟨21, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (83345828528021 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (223896706333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_22 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41655700924579 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119485546669 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨22, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41655700924579 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119485546669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_23 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (8327699933207 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119487532361 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨23, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (8327699933207 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119487532361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_24 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (10405327618017 / 12500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (279872387191 / 12500000000000 : ℝ))
      (E := (cell12804 ⟨24, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (10405327618017 / 12500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (279872387191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_25 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (2600258332903 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238983078139 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨25, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (2600258332903 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238983078139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_26 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (83173936426061 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238987067799 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨26, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (83173936426061 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238987067799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_27 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41569815115753 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238991069161 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨27, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41569815115753 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238991069161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_28 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (8310534803727 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238995084649 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨28, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (8310534803727 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238995084649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_29 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41535544905777 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447799823291 / 20000000000000 : ℝ))
      (E := (cell12804 ⟨29, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41535544905777 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447799823291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_30 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (3321474220909 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119501554007 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨30, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (3321474220909 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119501554007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_31 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (83002645139307 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119503559769 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨31, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (83002645139307 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119503559769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_32 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (20742114657497 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119505546979 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨32, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (20742114657497 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119505546979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_33 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (20733573990903 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239015149669 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨33, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (20733573990903 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239015149669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_34 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (1295314954831 / 1562500000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239019111941 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨34, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (1295314954831 / 1562500000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239019111941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_35 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41433021017933 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119511578689 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨35, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41433021017933 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119511578689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_36 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (3313278028519 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239027110663 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨36, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (3313278028519 / 4000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239027110663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_37 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16559576621997 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239031148091 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨37, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16559576621997 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239031148091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_38 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (82763839196523 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239035152467 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨38, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (82763839196523 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2239035152467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_39 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (20682454735593 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559759780913 / 25000000000000 : ℝ))
      (E := (cell12804 ⟨39, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (20682454735593 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559759780913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12805_20 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (8338027075549 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238843679233 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨20, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (8338027075549 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238843679233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_21 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16669164037869 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119423849579 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨21, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16669164037869 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119423849579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_22 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41655696908671 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (279856457199 / 12500000000000 : ℝ))
      (E := (cell12805 ⟨22, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41655696908671 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (279856457199 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_23 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (2602405987709 / 3125000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238855674773 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨23, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (2602405987709 / 3125000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238855674773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_24 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83242613524759 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447771939149 / 20000000000000 : ℝ))
      (E := (cell12805 ⟨24, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83242613524759 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447771939149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_25 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83208259539101 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119431861813 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨25, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83208259539101 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119431861813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_26 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41586964808711 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559716925719 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨26, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41586964808711 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559716925719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_27 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83139623727599 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238871694527 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨27, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83139623727599 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238871694527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_28 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (10388167729709 / 12500000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238875701003 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨28, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (10388167729709 / 12500000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238875701003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_29 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (20767770978961 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559719931123 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨29, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (20767770978961 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559719931123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_30 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (1037960624131 / 1250000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119441854217 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨30, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (1037960624131 / 1250000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119441854217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_31 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83002639850107 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559721928259 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨31, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83002639850107 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559721928259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_32 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82968453643413 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (11194458699 / 500000000000 : ℝ))
      (E := (cell12805 ⟨32, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82968453643413 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (11194458699 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_33 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82934291279243 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223889573141 / 10000000000000 : ℝ))
      (E := (cell12805 ⟨33, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82934291279243 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (223889573141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_34 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82900152726603 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238899747461 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨34, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82900152726603 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238899747461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_35 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16573207590931 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119451865069 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨35, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16573207590931 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119451865069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_36 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41415973466359 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119453869317 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨36, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41415973466359 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119453869317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_37 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41398939815133 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89556470933 / 4000000000000 : ℝ))
      (E := (cell12805 ⟨37, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41398939815133 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89556470933 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_38 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (82763836016927 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447783155131 / 20000000000000 : ℝ))
      (E := (cell12805 ⟨38, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (82763836016927 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (447783155131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_39 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16545963212497 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559729936371 / 25000000000000 : ℝ))
      (E := (cell12805 ⟨39, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16545963212497 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (559729936371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12806_20 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83380262111101 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238724325177 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨20, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83380262111101 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238724325177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_21 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (5209113240763 / 6250000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559682082799 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨21, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (5209113240763 / 6250000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559682082799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_22 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (20827846446757 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238732334763 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨22, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (20827846446757 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238732334763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_23 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (8327698388277 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559684084867 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨23, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (8327698388277 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559684084867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_24 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83242606106811 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119370174333 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨24, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83242606106811 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119370174333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_25 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (10401031553337 / 12500000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238744307069 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨25, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (10401031553337 / 12500000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238744307069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_26 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83173922810137 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238748334351 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨26, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83173922810137 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238748334351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_27 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (8313961722501 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (279844039541 / 12500000000000 : ℝ))
      (E := (cell12806 ⟨27, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (8313961722501 / 10000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (279844039541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_28 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (20776333909839 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (139922273269 / 6250000000000 : ℝ))
      (E := (cell12806 ⟨28, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (20776333909839 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (139922273269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_29 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41535539010689 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238760329041 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨29, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41535539010689 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238760329041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_30 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83036844339443 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119382181963 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨30, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83036844339443 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119382181963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_31 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83002634562079 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119384180833 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨31, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83002634562079 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119384180833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_32 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82968448657973 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447754476453 / 20000000000000 : ℝ))
      (E := (cell12806 ⟨32, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82968448657973 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447754476453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_33 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82934286595973 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559694092101 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨33, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82934286595973 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559694092101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_34 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16580029669017 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119390189839 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨34, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16580029669017 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119390189839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_35 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82866033874471 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238784358271 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨35, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82866033874471 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238784358271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_36 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (20707985788363 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (17910306907 / 800000000000 : ℝ))
      (E := (cell12806 ⟨36, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (20707985788363 / 25000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (17910306907 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_37 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82797876151501 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238792395367 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨37, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82797876151501 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238792395367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_38 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82763832838249 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (279849549461 / 12500000000000 : ℝ))
      (E := (cell12806 ⟨38, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82763832838249 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (279849549461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_39 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (82729813183479 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238800422933 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨39, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (82729813183479 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238800422933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12807_20 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (651408230221 / 781250000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559651241823 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨20, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (651408230221 / 781250000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559651241823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_21 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83345803516609 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559652254439 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨21, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83345803516609 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559652254439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_22 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16662275551643 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238613008183 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨22, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16662275551643 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238613008183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_23 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20819244040079 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238617000451 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨23, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20819244040079 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238617000451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_24 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (8324259869029 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (279827624739 / 12500000000000 : ℝ))
      (E := (cell12807 ⟨24, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (8324259869029 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (279827624739 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_25 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83208245315683 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447725000737 / 20000000000000 : ℝ))
      (E := (cell12807 ⟨25, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83208245315683 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447725000737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_26 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83173916004207 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119314510327 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨26, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83173916004207 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119314510327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_27 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41569805361869 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111931649651 / 5000000000000 : ℝ))
      (E := (cell12807 ⟨27, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41569805361869 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111931649651 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_28 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (1038816618029 / 1250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119318520041 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨28, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (1038816618029 / 1250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119318520041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_29 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20767768032039 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238641047101 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨29, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20767768032039 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238641047101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_30 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83036838749613 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238645015967 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨30, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83036838749613 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238645015967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_31 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83002629275221 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559662251721 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨31, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83002629275221 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559662251721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_32 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20742110918417 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119326510677 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨32, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20742110918417 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119326510677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_33 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41467140956901 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559664265163 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨33, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41467140956901 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559664265163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_34 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82900143964629 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (223866106721 / 10000000000000 : ℝ))
      (E := (cell12807 ⟨34, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82900143964629 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (223866106721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_35 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82866029795313 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111933252089 / 5000000000000 : ℝ))
      (E := (cell12807 ⟨35, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82866029795313 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (111933252089 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_36 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (3313277575007 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119334521777 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨36, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (3313277575007 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119334521777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_37 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (8279787267369 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119336536453 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨37, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (8279787267369 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119336536453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_38 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (82763829660489 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119338535639 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨38, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (82763829660489 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119338535639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_39 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16545962061071 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119340548633 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨39, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16545962061071 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119340548633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12808_20 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83380244827049 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (17488169249 / 781250000000 : ℝ))
      (E := (cell12808 ⟨20, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83380244827049 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (17488169249 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_21 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83345795182547 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238489700531 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨21, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83345795182547 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238489700531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_22 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41655684865451 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447698735571 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨22, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41655684865451 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447698735571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_23 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41638484219663 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (27981221451 / 1250000000000 : ℝ))
      (E := (cell12808 ⟨23, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41638484219663 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (27981221451 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_24 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20810647818799 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119250850933 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨24, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20810647818799 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119250850933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_25 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (4160411910303 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279813212083 / 12500000000000 : ℝ))
      (E := (cell12808 ⟨25, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (4160411910303 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (279813212083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_26 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (8317390919963 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238509703359 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨26, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (8317390919963 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238509703359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_27 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (10392450527973 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119256862301 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨27, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (10392450527973 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119256862301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_28 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (20776330811641 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (139907356521 / 6250000000000 : ℝ))
      (E := (cell12808 ⟨28, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (20776330811641 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (139907356521 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_29 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41535533118089 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (89540868127 / 4000000000000 : ℝ))
      (E := (cell12808 ⟨29, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41535533118089 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (89540868127 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_30 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83036833160991 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119262861541 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨30, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83036833160991 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119262861541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_31 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (16600524797907 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559632426809 / 25000000000000 : ℝ))
      (E := (cell12808 ⟨31, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (16600524797907 / 20000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559632426809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_32 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82968438690497 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238533715639 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨32, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82968438690497 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238533715639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_33 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (10366784654091 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447707549913 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨33, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (10366784654091 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447707549913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_34 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41450069792617 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238541751443 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨34, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41450069792617 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238541751443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_35 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (4143301285859 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238545722027 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨35, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (4143301285859 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238545722027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_36 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (82831935597887 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238549779171 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨36, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (82831935597887 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238549779171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_37 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (2587433412401 / 3125000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238553747257 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨37, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (2587433412401 / 3125000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238553747257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_38 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41381913241823 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238557743717 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨38, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41381913241823 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238557743717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_39 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (5170612964257 / 6250000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238561768483 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨39, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (5170612964257 / 6250000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238561768483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12809_20 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (10422529523423 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559591603729 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨20, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (10422529523423 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559591603729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_21 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83345786850023 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238370437829 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨21, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83345786850023 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238370437829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_22 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83311361705091 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (34974600033 / 1562500000000 : ℝ))
      (E := (cell12809 ⟨22, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83311361705091 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (34974600033 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_23 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (416384803599 / 500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119189213999 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨23, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (416384803599 / 500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119189213999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_24 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83242583861529 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238382402147 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨24, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83242583861529 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238382402147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_25 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83208231097827 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119193222207 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨25, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83208231097827 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119193222207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_26 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (41586951198203 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (34974850639 / 1562500000000 : ℝ))
      (E := (cell12809 ⟨26, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (41586951198203 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (34974850639 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_27 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (16627919545029 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (17907155621 / 800000000000 : ℝ))
      (E := (cell12809 ⟨27, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (16627919545029 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (17907155621 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_28 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83105317052089 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238398423541 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨28, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83105317052089 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238398423541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_29 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83071060345443 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238402472763 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨29, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83071060345443 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238402472763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_30 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (10379603446697 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559601606687 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨30, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (10379603446697 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559601606687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_31 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83002618705019 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238410462723 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨31, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83002618705019 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238410462723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_32 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82968433708461 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (13990090407 / 625000000000 : ℝ))
      (E := (cell12809 ⟨32, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82968433708461 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (13990090407 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_33 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82934272552753 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238418493733 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨33, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82934272552753 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238418493733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_34 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82900135206901 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119211245497 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨34, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82900135206901 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119211245497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_35 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82866021640073 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238426457651 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨35, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82866021640073 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238426457651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_36 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82831931821589 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119215226449 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨36, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82831931821589 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119215226449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_37 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82797865720927 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119217238553 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨37, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82797865720927 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119217238553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_38 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82763823307719 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559609617929 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨38, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82763823307719 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559609617929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_39 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (82729804551751 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238442495319 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨39, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (82729804551751 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238442495319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12810_20 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83380227549293 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (279780895267 / 12500000000000 : ℝ))
      (E := (cell12810 ⟨20, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83380227549293 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (279780895267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_21 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (16669155703807 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238251171343 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨21, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (16669155703807 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238251171343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_22 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83311353680779 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559563795239 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨22, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83311353680779 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559563795239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_23 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10409619125217 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119129597283 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨23, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10409619125217 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119129597283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_24 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10405322056161 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238263157137 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨24, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10405322056161 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238263157137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_25 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83208223990983 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238267188529 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨25, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83208223990983 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238267188529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_26 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (16634779118907 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119135587417 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨26, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (16634779118907 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119135587417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_27 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (5196224451739 / 6250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119137588543 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨27, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (5196224451739 / 6250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119137588543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_28 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83105310858893 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238279197701 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨28, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83105310858893 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238279197701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_29 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (5191940903497 / 6250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447656636073 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨29, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (5191940903497 / 6250000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447656636073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_30 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10379602748421 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238287185489 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨30, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10379602748421 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238287185489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_31 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83002613421673 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238291214801 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨31, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83002613421673 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238291214801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_32 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82968428727559 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238295211227 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨32, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82968428727559 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238295211227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_33 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (663474142991 / 800000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447659846913 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨33, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (663474142991 / 800000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447659846913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_34 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (8290013082963 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559575806811 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨34, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (8290013082963 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559575806811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_35 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (82866017563991 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119153624327 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨35, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (82866017563991 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119153624327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_36 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (2070798201157 / 2500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238311240727 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨36, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (2070798201157 / 2500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238311240727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_37 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10349732780747 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119157631227 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨37, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10349732780747 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119157631227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_38 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (8276382013271 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238319255273 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨38, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (8276382013271 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238319255273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_39 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (8272980167627 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (139895204861 / 6250000000000 : ℝ))
      (E := (cell12810 ⟨39, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (8272980167627 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (139895204861 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12811_20 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (10422527364097 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119063981911 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨20, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (10422527364097 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119063981911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_21 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (16669154037917 / 20000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119065979691 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨21, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (16669154037917 / 20000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119065979691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_22 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83311345657967 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119067978027 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨22, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83311345657967 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119067978027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_23 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (5204809080321 / 6250000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119069978711 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨23, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (5204809080321 / 6250000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119069978711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_24 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41621284519237 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238143966837 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨24, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41621284519237 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238143966837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_25 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83208216885529 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447629597483 / 20000000000000 : ℝ))
      (E := (cell12811 ⟨25, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83208216885529 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447629597483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_26 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (2599184024813 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119075981803 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨26, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (2599184024813 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119075981803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_27 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41569792365909 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238155956441 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨27, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41569792365909 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238155956441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_28 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83105304666977 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238159968339 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨28, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83105304666977 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238159968339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_29 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83071048567703 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559541000371 / 25000000000000 : ℝ))
      (E := (cell12811 ⟨29, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83071048567703 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559541000371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_30 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41518408201183 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559541999827 / 25000000000000 : ℝ))
      (E := (cell12811 ⟨30, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41518408201183 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559541999827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_31 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41501304069749 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119086011007 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨31, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41501304069749 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119086011007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_32 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (8296842374779 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559544003133 / 25000000000000 : ℝ))
      (E := (cell12811 ⟨32, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (8296842374779 / 10000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559544003133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_33 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41467131598047 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (34971562979 / 1562500000000 : ℝ))
      (E := (cell12811 ⟨33, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41467131598047 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (34971562979 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_34 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82900126453419 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119092009407 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨34, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82900126453419 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119092009407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_35 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82866013488933 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238188036397 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨35, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82866013488933 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238188036397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_36 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82831924271959 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119096012667 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨36, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82831924271959 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119096012667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_37 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (10349732346497 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279774505577 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨37, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (10349732346497 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279774505577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_38 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82763816958617 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238200035681 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨38, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82763816958617 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238200035681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_39 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (82729798801669 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238204057121 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨39, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (82729798801669 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238204057121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12812_20 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (10422526284729 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119004380843 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨20, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (10422526284729 / 12500000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119004380843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_21 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (8334576186167 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (69937900061 / 3125000000000 : ℝ))
      (E := (cell12812 ⟨21, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (8334576186167 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (69937900061 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_22 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41655668818327 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119008392871 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨22, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41655668818327 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119008392871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_23 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41638468784999 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238020774931 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨23, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41638468784999 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238020774931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_24 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (16648512325817 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559506193217 / 25000000000000 : ℝ))
      (E := (cell12812 ⟨24, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (16648512325817 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559506193217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_25 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83208209781463 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238028782669 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨25, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83208209781463 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238028782669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_26 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (1663477639897 / 2000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238032807213 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨26, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (1663477639897 / 2000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238032807213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_27 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83139578237127 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238036790693 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨27, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83139578237127 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238036790693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_28 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (4155264923817 / 5000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119020396967 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨28, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (4155264923817 / 5000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119020396967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_29 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83071042680697 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238044819119 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨29, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83071042680697 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238044819119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_30 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (8303681081857 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238048809681 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨30, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (8303681081857 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238048809681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_31 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83002602858491 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238052825821 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨31, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83002602858491 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238052825821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_32 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41484209384577 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238056810467 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨32, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41484209384577 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238056810467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_33 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (8293425851941 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119030411707 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨33, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (8293425851941 / 10000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119030411707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_34 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82900122078269 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139879050443 / 6250000000000 : ℝ))
      (E := (cell12812 ⟨34, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82900122078269 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (139879050443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_35 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (828660094149 / 1000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238068820879 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨35, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (828660094149 / 1000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238068820879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_36 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82831920498627 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119036432691 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨36, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82831920498627 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119036432691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_37 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82797855298929 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (279759602949 / 12500000000000 : ℝ))
      (E := (cell12812 ⟨37, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82797855298929 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (279759602949 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_38 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82763813785441 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238080871651 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨38, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82763813785441 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238080871651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_39 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (82729795927949 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238084833353 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨39, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (82729795927949 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2238084833353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12813_20 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83380201644461 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118944807009 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨20, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83380201644461 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118944807009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_21 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83345753535291 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237893640737 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨21, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83345753535291 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237893640737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_22 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (2082783240421 / 2500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559474402921 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨22, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (2082783240421 / 2500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559474402921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_23 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41638464928161 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237901647091 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨23, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41638464928161 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237901647091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_24 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83242554221121 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559476408403 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨24, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83242554221121 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559476408403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_25 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41604101339393 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279738704087 / 12500000000000 : ℝ))
      (E := (cell12813 ⟨25, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41604101339393 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279738704087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_26 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20793468799259 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237913647223 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨26, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20793468799259 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237913647223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_27 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (10392446467969 / 12500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237917621387 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨27, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (10392446467969 / 12500000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237917621387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_28 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83105292286981 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447584334897 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨28, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83105292286981 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447584334897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_29 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83071036794933 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279740704159 / 12500000000000 : ℝ))
      (E := (cell12813 ⟨29, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83071036794933 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279740704159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_30 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (4151840261799 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237929675131 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨30, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (4151840261799 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237929675131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_31 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (16600519515731 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118966842383 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨31, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (16600519515731 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118966842383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_32 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82968413791651 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118968831801 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨32, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82968413791651 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118968831801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_33 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82934253843823 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237941671431 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨33, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82934253843823 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237941671431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_34 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (4145005885209 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118972825341 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨34, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (4145005885209 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118972825341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_35 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20716501335473 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118974830371 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨35, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20716501335473 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118974830371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_36 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82831916726283 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237953702207 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨36, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82831916726283 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237953702207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_37 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (41398925913417 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118978858379 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨37, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (41398925913417 / 50000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118978858379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_38 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (4138190530659 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279745213059 / 12500000000000 : ℝ))
      (E := (cell12813 ⟨38, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (4138190530659 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (279745213059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_39 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (82729793055109 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118982861971 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨39, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (82729793055109 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118982861971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12814_20 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41690096506331 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237770520821 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨20, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41690096506331 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237770520821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_21 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (5209109075653 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118887237871 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨21, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (5209109075653 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118887237871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_22 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (3332452863941 / 4000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118889246109 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨22, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (3332452863941 / 4000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118889246109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_23 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (20819230536027 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118891257773 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨23, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (20819230536027 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118891257773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_24 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41621273407291 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237786490687 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨24, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41621273407291 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237786490687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_25 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41604097788749 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (179023243 / 8000000000 : ℝ))
      (E := (cell12814 ⟨25, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41604097788749 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (179023243 / 8000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_26 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83173868400573 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279724317759 / 12500000000000 : ℝ))
      (E := (cell12814 ⟨26, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83173868400573 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279724317759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_27 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (20784891312923 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237798506979 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨27, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (20784891312923 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237798506979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_28 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83105286098901 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237802551519 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨28, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83105286098901 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237802551519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_29 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83071030910411 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447561300489 / 20000000000000 : ℝ))
      (E := (cell12814 ⟨29, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83071030910411 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447561300489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_30 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16607359930919 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (111890526857 / 5000000000000 : ℝ))
      (E := (cell12814 ⟨30, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16607359930919 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (111890526857 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_31 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83002592299987 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118907270153 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨31, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83002592299987 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118907270153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_32 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82968408815281 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237818513367 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨32, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82968408815281 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237818513367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_33 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (20733562292333 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279727821839 / 12500000000000 : ℝ))
      (E := (cell12814 ⟨33, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (20733562292333 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279727821839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_34 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82900113331151 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2797283187 / 125000000000 : ℝ))
      (E := (cell12814 ⟨34, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82900113331151 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2797283187 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_35 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82866001269907 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237830555991 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨35, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82866001269907 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237830555991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_36 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82831912954927 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (559458633953 / 25000000000000 : ℝ))
      (E := (cell12814 ⟨36, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82831912954927 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (559458633953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_37 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82797848355691 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237838548053 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨37, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82797848355691 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237838548053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_38 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16552761488367 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237842592859 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨38, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16552761488367 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237842592859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_39 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (82729790183149 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237846552687 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨39, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (82729790183149 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237846552687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12815_20 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16676036876487 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559412855951 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨20, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16676036876487 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559412855951 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_21 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (4167286844357 / 5000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (223765542359 / 10000000000000 : ℝ))
      (E := (cell12815 ⟨21, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (4167286844357 / 5000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (223765542359 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_22 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20827828395427 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447531885469 / 20000000000000 : ℝ))
      (E := (cell12815 ⟨22, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20827828395427 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447531885469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_23 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20819228608339 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237663380293 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨23, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20819228608339 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237663380293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_24 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20810634852367 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237667402477 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨24, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20810634852367 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237667402477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_25 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83208188477597 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237671438673 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨25, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83208188477597 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237671438673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_26 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41586930802731 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118837716663 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨26, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41586930802731 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118837716663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_27 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41569779380473 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237679447469 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨27, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41569779380473 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237679447469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_28 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83105279912099 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118841712517 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨28, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83105279912099 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118841712517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_29 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (8307102502713 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237687426637 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨29, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (8307102502713 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237687426637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_30 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16607358814883 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559422863557 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨30, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16607358814883 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559422863557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_31 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (10375323377811 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118847725493 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨31, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (10375323377811 / 12500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118847725493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_32 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20742100960011 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118849709167 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨32, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20742100960011 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118849709167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_33 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82934244495937 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885173733 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨33, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82934244495937 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885173733 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_34 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82900108959181 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237707445223 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨34, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82900108959181 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237707445223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_35 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41432998599473 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885572399 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨35, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41432998599473 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885572399 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_36 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41415954592279 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118857741763 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨36, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41415954592279 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118857741763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_37 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (82797844885499 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885974677 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨37, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (82797844885499 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111885974677 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_38 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16552760854281 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (22377234781 / 1000000000000 : ℝ))
      (E := (cell12815 ⟨38, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16552760854281 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (22377234781 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_39 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20682446828017 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (139857968487 / 6250000000000 : ℝ))
      (E := (cell12815 ⟨39, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20682446828017 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (139857968487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12816_20 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (4169008787689 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279691540371 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨20, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (4169008787689 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279691540371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_21 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41672864282683 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447507261869 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨21, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41672864282683 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447507261869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_22 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83311305566389 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (223754035873 / 10000000000000 : ℝ))
      (E := (cell12816 ⟨22, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83311305566389 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (223754035873 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_23 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (2602403335127 / 3125000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279693044757 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨23, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (2602403335127 / 3125000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279693044757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_24 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41621266002889 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237548368983 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨24, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41621266002889 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237548368983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_25 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (20802045344771 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447510467243 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨25, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (20802045344771 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447510467243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_26 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83173854811701 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (111877818971 / 5000000000000 : ℝ))
      (E := (cell12816 ⟨26, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83173854811701 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (111877818971 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_27 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (16627910454303 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237560325949 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨27, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (16627910454303 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237560325949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_28 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41552636863287 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237564353509 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨28, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41552636863287 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237564353509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_29 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83071019145091 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237568347349 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨29, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83071019145091 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237568347349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_30 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (1037959856193 / 1250000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118786183937 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨30, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (1037959856193 / 1250000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118786183937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_31 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83002581746157 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237576358261 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨31, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83002581746157 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237576358261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_32 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41484199432969 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279697547313 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨32, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41484199432969 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279697547313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_33 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41467119911819 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237584371277 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨33, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41467119911819 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237584371277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_34 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82900104588271 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237588396169 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨34, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82900104588271 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237588396169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_35 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (5179124570563 / 6250000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447518479071 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨35, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (5179124570563 / 6250000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447518479071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_36 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (10353988176897 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447519273871 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨36, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (10353988176897 / 12500000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447519273871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_37 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41398920708129 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559400094289 / 25000000000000 : ℝ))
      (E := (cell12816 ⟨37, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41398920708129 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559400094289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_38 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (82763801101891 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279700552363 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨38, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (82763801101891 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279700552363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_39 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41364892220933 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237608435787 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨39, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41364892220933 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237608435787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12817_20 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16676033425339 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (34959582447 / 1562500000000 : ℝ))
      (E := (cell12817 ⟨20, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16676033425339 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (34959582447 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_21 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83345720245127 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559354326987 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨21, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83345720245127 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559354326987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_22 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83311297552567 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118710643187 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨22, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83311297552567 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118710643187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_23 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83276899016233 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237425273757 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨23, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83276899016233 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237425273757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_24 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10405315575439 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139839333239 / 6250000000000 : ℝ))
      (E := (cell12817 ⟨24, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10405315575439 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139839333239 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_25 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41604087140979 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237433288537 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨25, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41604087140979 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237433288537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_26 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83173848019291 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237437321923 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨26, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83173848019291 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237437321923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_27 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41569772891699 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447488263557 / 20000000000000 : ℝ))
      (E := (cell12817 ⟨27, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41569772891699 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447488263557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_28 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83105267542327 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118722668473 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨28, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83105267542327 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118722668473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_29 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83071013264293 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237449323083 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨29, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83071013264293 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237449323083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_30 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83036782917669 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559363334151 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨30, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83036782917669 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559363334151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_31 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41501288235497 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237457320681 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨31, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41501288235497 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237457320681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_32 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20742098473241 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559365333827 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨32, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20742098473241 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559365333827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_33 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16586847030487 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (55936633079 / 2500000000000 : ℝ))
      (E := (cell12817 ⟨33, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16586847030487 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (55936633079 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_34 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82900100218421 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139841833989 / 6250000000000 : ℝ))
      (E := (cell12817 ⟨34, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82900100218421 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139841833989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_35 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82865989060093 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (89498933579 / 4000000000000 : ℝ))
      (E := (cell12817 ⟨35, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82865989060093 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (89498933579 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_36 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82831901646781 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139842335581 / 6250000000000 : ℝ))
      (E := (cell12817 ⟨36, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82831901646781 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (139842335581 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_37 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (1293716217937 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (279685171871 / 12500000000000 : ℝ))
      (E := (cell12817 ⟨37, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (1293716217937 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (279685171871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_38 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20690949483323 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447497071313 / 20000000000000 : ℝ))
      (E := (cell12817 ⟨38, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20690949483323 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447497071313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_39 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (82729781572543 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559372343169 / 25000000000000 : ℝ))
      (E := (cell12817 ⟨39, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (82729781572543 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (559372343169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12818_20 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41690079250591 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237294284719 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨20, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41690079250591 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237294284719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_21 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41672855963211 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559324575693 / 25000000000000 : ℝ))
      (E := (cell12818 ⟨21, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41672855963211 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559324575693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_22 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41655644770121 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118651134307 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨22, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41655644770121 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118651134307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_23 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41638445654931 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118653151237 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨23, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41638445654931 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118653151237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_24 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83242517202669 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237310291 / 100000000000 : ℝ))
      (E := (cell12818 ⟨24, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83242517202669 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237310291 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_25 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41604083593109 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237314295639 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨25, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41604083593109 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237314295639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_26 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83173841228231 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118659159633 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨26, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83173841228231 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118659159633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_27 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41569769648297 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237322306069 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨27, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41569769648297 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237322306069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_28 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83105261359357 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237326316867 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨28, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83105261359357 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237326316867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_29 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (16614201476947 / 20000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (111866514767 / 5000000000000 : ℝ))
      (E := (cell12818 ⟨29, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (16614201476947 / 20000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (111866514767 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_30 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83036777341103 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559333575473 / 25000000000000 : ℝ))
      (E := (cell12818 ⟨30, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83036777341103 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559333575473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_31 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83002571196999 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559334584561 / 25000000000000 : ℝ))
      (E := (cell12818 ⟨31, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83002571196999 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559334584561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_32 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41484194460561 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237342347317 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨32, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41484194460561 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237342347317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_33 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41467115241163 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237346330309 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨33, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41467115241163 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237346330309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_34 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82900095849629 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447470069361 / 20000000000000 : ℝ))
      (E := (cell12818 ⟨34, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82900095849629 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (447470069361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_35 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41432992496101 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (111867716949 / 5000000000000 : ℝ))
      (E := (cell12818 ⟨35, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41432992496101 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (111867716949 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_36 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41415948939687 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118679183009 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨36, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41415948939687 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118679183009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_37 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82797834480629 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237362369599 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨37, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82797834480629 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237362369599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_38 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82763794765607 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118683174897 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨38, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82763794765607 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118683174897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_39 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (82729778704099 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237370365193 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨39, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (82729778704099 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237370365193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12819_20 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83380149877239 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237175289017 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨20, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83380149877239 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237175289017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_21 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (333382814437 / 400000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (111858964691 / 5000000000000 : ℝ))
      (E := (cell12819 ⟨21, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (333382814437 / 400000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (111858964691 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_22 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41655640764707 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559295826363 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨22, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41655640764707 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559295826363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_23 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83276883604951 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237187327491 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨23, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83276883604951 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237187327491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_24 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83242509803249 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237191304897 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨24, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83242509803249 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237191304897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_25 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (16641632018373 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447439059823 / 20000000000000 : ℝ))
      (E := (cell12819 ⟨25, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (16641632018373 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447439059823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_26 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83173834438521 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237199313021 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨26, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83173834438521 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237199313021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_27 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83139532811103 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (279650418657 / 12500000000000 : ℝ))
      (E := (cell12819 ⟨27, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83139532811103 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (279650418657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_28 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83105255177663 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118603675877 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨28, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83105255177663 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118603675877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_29 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83071001506417 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237211322623 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨29, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83071001506417 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237211322623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_30 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (4151838588287 / 5000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237215322267 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨30, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (4151838588287 / 5000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237215322267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_31 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (20750641481043 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118609676203 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨31, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (20750641481043 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118609676203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_32 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (8296838395041 / 10000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118611677981 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨32, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (8296838395041 / 10000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118611677981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_33 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (82934225813313 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (223722733413 / 10000000000000 : ℝ))
      (E := (cell12819 ⟨33, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (82934225813313 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (223722733413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_34 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10362511435237 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (34956739789 / 1562500000000 : ℝ))
      (E := (cell12819 ⟨34, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10362511435237 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (34956739789 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_35 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (20716495231333 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (17897883151 / 800000000000 : ℝ))
      (E := (cell12819 ⟨35, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (20716495231333 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (17897883151 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_36 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10353986764119 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118619679763 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨36, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10353986764119 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118619679763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_37 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (517486443839 / 625000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237243361051 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨37, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (517486443839 / 625000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237243361051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_38 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (20690947899709 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237247398593 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨38, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (20690947899709 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237247398593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_39 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41364887918267 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118625706669 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨39, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41364887918267 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118625706669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12820_20 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41690070627433 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223705634779 / 10000000000000 : ℝ))
      (E := (cell12820 ⟨20, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41690070627433 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223705634779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_21 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83345695293611 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447412067881 / 20000000000000 : ℝ))
      (E := (cell12820 ⟨21, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83345695293611 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447412067881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_22 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41655636760041 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (44741286771 / 2000000000000 : ℝ))
      (E := (cell12820 ⟨22, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41655636760041 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (44741286771 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_23 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83276875901499 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118534174403 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨23, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83276875901499 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118534174403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_24 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (20810625601313 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237072373513 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨24, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (20810625601313 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237072373513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_25 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41604076499449 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559269089343 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨25, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41604076499449 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559269089343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_26 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (1039672845627 / 1250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237080361617 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨26, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (1039672845627 / 1250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237080361617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_27 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (3325581053077 / 4000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237084388891 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨27, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (3325581053077 / 4000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237084388891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_28 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41552624498623 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (3579341413 / 160000000000 : ℝ))
      (E := (cell12820 ⟨28, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41552624498623 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (3579341413 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_29 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83070995629339 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237092404929 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨29, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83070995629339 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237092404929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_30 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83036766191581 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118548198863 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨30, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83036766191581 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118548198863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_31 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (2593830020391 / 3125000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237100421713 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨31, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (2593830020391 / 3125000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237100421713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_32 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (8296837898083 / 10000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237104419813 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨32, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (8296837898083 / 10000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237104419813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_33 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41467110572697 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118554196609 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨33, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41467110572697 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118554196609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_34 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82900087115221 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118556200757 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨34, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82900087115221 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118556200757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_35 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (16573195371897 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559279111379 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨35, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (16573195371897 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559279111379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_36 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82831890347517 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (13982002553 / 625000000000 : ℝ))
      (E := (cell12820 ⟨36, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82831890347517 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (13982002553 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_37 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (82797827548801 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237124408011 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨37, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (82797827548801 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237124408011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_38 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (4138189421649 / 5000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279641055531 / 12500000000000 : ℝ))
      (E := (cell12820 ⟨38, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (4138189421649 / 5000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279641055531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_39 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41364886484923 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237132458379 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨39, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41364886484923 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237132458379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12821_20 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83380132634063 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (8947749611 / 400000000000 : ℝ))
      (E := (cell12821 ⟨20, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83380132634063 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (8947749611 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_21 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16669137395901 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236941439529 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨21, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16669137395901 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236941439529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_22 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16662253102449 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1789556341 / 80000000000 : ℝ))
      (E := (cell12821 ⟨22, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16662253102449 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1789556341 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_23 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41638434099753 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118474712391 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨23, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41638434099753 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118474712391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_24 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41621247504339 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236953438467 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨24, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41621247504339 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236953438467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_25 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83208145907317 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559239367603 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨25, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83208145907317 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559239367603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_26 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20793455215787 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118480732529 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨26, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20793455215787 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118480732529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_27 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83139519844059 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236965483433 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨27, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83139519844059 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236965483433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_28 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16621048563621 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236969469463 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨28, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16621048563621 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236969469463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_29 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (166141979507 / 200000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236973483761 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨29, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (166141979507 / 200000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236973483761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_30 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (664294084949 / 800000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559244367437 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨30, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (664294084949 / 800000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559244367437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_31 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41501277691009 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118490743811 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨31, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41501277691009 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118490743811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_32 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (4148418700619 / 5000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236985480301 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨32, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (4148418700619 / 5000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236985480301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_33 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82934216478569 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279623688447 / 12500000000000 : ℝ))
      (E := (cell12821 ⟨33, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82934216478569 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (279623688447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_34 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20725020687401 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236993511863 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨34, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20725020687401 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236993511863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_35 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (4143298639733 / 5000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447399498781 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨35, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (4143298639733 / 5000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447399498781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_36 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82831886583067 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237001512887 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨36, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82831886583067 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237001512887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_37 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82797824084313 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118502755241 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨37, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82797824084313 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118502755241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_38 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41381892634019 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237009486763 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨38, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41381892634019 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2237009486763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_39 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (82729770104037 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447402700063 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨39, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (82729770104037 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447402700063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12822_20 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83380124014829 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236818512189 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨20, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83380124014829 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236818512189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_21 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83345678666931 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118411267939 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨21, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83345678666931 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118411267939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_22 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16662251501181 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236826568549 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨22, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16662251501181 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236826568549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_23 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20819215124743 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (111841527771 / 5000000000000 : ℝ))
      (E := (cell12822 ⟨23, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20819215124743 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (111841527771 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_24 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (3329699504541 / 4000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (34950539971 / 1562500000000 : ℝ))
      (E := (cell12822 ⟨24, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (3329699504541 / 4000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (34950539971 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_25 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83208138817121 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559209644957 / 25000000000000 : ℝ))
      (E := (cell12822 ⟨25, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83208138817121 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559209644957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_26 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16634762815497 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236842564913 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨26, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16634762815497 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236842564913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_27 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41569756681253 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279605821803 / 12500000000000 : ℝ))
      (E := (cell12822 ⟨27, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41569756681253 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279605821803 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_28 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83105236640239 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (223685055229 / 10000000000000 : ℝ))
      (E := (cell12822 ⟨28, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83105236640239 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (223685055229 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_29 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83070983878901 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236854559119 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨29, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83070983878901 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236854559119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_30 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (10379594380859 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118429298429 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨30, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (10379594380859 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118429298429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_31 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83002550112691 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118431304339 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨31, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83002550112691 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118431304339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_32 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (4148418452253 / 5000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236866595999 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨32, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (4148418452253 / 5000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236866595999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_33 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41467105906419 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139804413663 / 6250000000000 : ℝ))
      (E := (cell12822 ⟨33, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41467105906419 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139804413663 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_34 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16580015677009 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236874618923 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨34, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16580015677009 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236874618923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_35 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (10358246091357 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118439298843 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨35, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (10358246091357 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118439298843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_36 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82831882819603 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118441307039 / 50000000000000 : ℝ))
      (E := (cell12822 ⟨36, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82831882819603 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (1118441307039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_37 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82797820620773 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139805413111 / 6250000000000 : ℝ))
      (E := (cell12822 ⟨37, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82797820620773 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139805413111 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_38 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (82763782104009 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236890643561 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨38, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (82763782104009 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236890643561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_39 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16545953447821 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236894597883 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨39, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16545953447821 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236894597883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12823_20 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20845028849291 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118349838053 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨20, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20845028849291 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118349838053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_21 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83345670355889 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (139793980423 / 6250000000000 : ℝ))
      (E := (cell12823 ⟨21, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83345670355889 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (139793980423 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_22 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83311249501059 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118353853557 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨22, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83311249501059 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118353853557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_23 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83276852799897 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (55917792059 / 2500000000000 : ℝ))
      (E := (cell12823 ⟨23, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83276852799897 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (55917792059 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_24 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41621240109897 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236715674161 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨24, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41621240109897 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236715674161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_25 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (8320813172831 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118359842811 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨25, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (8320813172831 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118359842811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_26 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (8317380729317 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118361859807 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨26, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (8317380729317 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118361859807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_27 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (16627901376453 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118363860161 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨27, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (16627901376453 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118363860161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_28 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83105230463649 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559182922521 / 25000000000000 : ℝ))
      (E := (cell12823 ⟨28, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83105230463649 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559182922521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_29 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83070978005541 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447347137901 / 20000000000000 : ℝ))
      (E := (cell12823 ⟨29, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83070978005541 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447347137901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_30 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83036749476321 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236739720533 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨30, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83036749476321 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236739720533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_31 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (8300254484453 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (8737280181 / 390625000000 : ℝ))
      (E := (cell12823 ⟨31, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (8300254484453 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (8737280181 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_32 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (8296836407887 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447349541667 / 20000000000000 : ℝ))
      (E := (cell12823 ⟨32, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (8296836407887 / 10000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447349541667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_33 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82934207148201 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559187931579 / 25000000000000 : ℝ))
      (E := (cell12823 ⟨33, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82934207148201 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559187931579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_34 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (10362509252693 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447351144539 / 20000000000000 : ℝ))
      (E := (cell12823 ⟨34, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (10362509252693 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (447351144539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_35 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41432982334037 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236759756857 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨35, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41432982334037 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236759756857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_36 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (662655032457 / 800000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236763770721 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨36, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (662655032457 / 800000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236763770721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_37 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82797817158183 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118383882291 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨37, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82797817158183 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118383882291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_38 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82763778940893 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559192934627 / 25000000000000 : ℝ))
      (E := (cell12823 ⟨38, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82763778940893 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559192934627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_39 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (82729764375051 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236775751083 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨39, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (82729764375051 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236775751083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12824_20 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83380106781067 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447316167243 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨20, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83380106781067 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447316167243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_21 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83345662046379 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118292416943 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨21, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83345662046379 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118292416943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_22 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20827810374427 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279573605243 / 12500000000000 : ℝ))
      (E := (cell12824 ⟨22, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20827810374427 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (279573605243 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_23 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83276845102279 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447318572793 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨23, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83276845102279 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447318572793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_24 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16648494565497 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118298422451 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨24, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16648494565497 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118298422451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_25 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20802031160221 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236600846201 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨25, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20802031160221 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236600846201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_26 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83173800510203 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236604870731 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨26, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83173800510203 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236604870731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_27 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16627900080667 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118304431337 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨27, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16627900080667 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118304431337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_28 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41552612144167 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118306441423 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨28, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41552612144167 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118306441423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_29 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83070972133419 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236616874921 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨29, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83070972133419 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236616874921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_30 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20759185976743 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118310449649 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨30, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20759185976743 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118310449649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_31 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16600507915507 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447324979829 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨31, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16600507915507 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447324979829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_32 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82968359113809 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236628875883 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨32, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82968359113809 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236628875883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_33 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41467101242329 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447326577859 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨33, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41467101242329 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447326577859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_34 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (829000696591 / 1000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236636881801 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨34, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (829000696591 / 1000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236636881801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_35 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82865960606313 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111832045639 / 5000000000000 : ℝ))
      (E := (cell12824 ⟨35, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82865960606313 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111832045639 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_36 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82831875295631 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236644924153 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨36, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82831875295631 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236644924153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_37 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41398906848271 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236648916213 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨37, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41398906848271 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236648916213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_38 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (82763775778691 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111832647387 / 5000000000000 : ℝ))
      (E := (cell12824 ⟨38, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (82763775778691 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (111832647387 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_39 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41364880755937 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118328450591 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨39, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41364880755937 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118328450591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

end BstLean.Part268
