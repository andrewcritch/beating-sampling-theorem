import BstLean.Part268CellShard18Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12800_0 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (21018622331043 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239360912097 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨0, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (21018622331043 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239360912097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_1 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (84039546139147 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239364879347 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨1, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (84039546139147 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239364879347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_2 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (84004627843421 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239368889349 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨2, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (84004627843421 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239368889349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_3 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8396973440059 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (13996080581 / 625000000000 : ℝ))
      (E := (cell12800 ⟨3, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8396973440059 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (13996080581 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_4 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83934865774443 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (11196884493 / 500000000000 : ℝ))
      (E := (cell12800 ⟨4, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83934865774443 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (11196884493 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_5 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41950010964481 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (223938091443 / 10000000000000 : ℝ))
      (E := (cell12800 ⟨5, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41950010964481 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (223938091443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_6 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83865202828313 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2799231113 / 125000000000 : ℝ))
      (E := (cell12800 ⟨6, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83865202828313 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2799231113 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_7 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (16766081687371 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239388892073 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨7, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (16766081687371 / 20000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239388892073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_8 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8379563871913 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559848217211 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨8, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8379563871913 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559848217211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_9 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (20940223409967 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239396885819 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨9, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (20940223409967 / 25000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239396885819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_10 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83726173163981 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559850222961 / 25000000000000 : ℝ))
      (E := (cell12800 ⟨10, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83726173163981 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (559850222961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_11 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83691477256567 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239404893491 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨11, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83691477256567 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239404893491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_12 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41828402941451 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239408897093 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨12, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41828402941451 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239408897093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_13 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83622159008447 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239412908727 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨13, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83622159008447 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239412908727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_14 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83587536598839 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239416934229 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨14, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83587536598839 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239416934229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_15 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (10444117327487 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279927615127 / 12500000000000 : ℝ))
      (E := (cell12800 ⟨15, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (10444117327487 / 12500000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279927615127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_16 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (8351836503761 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (27992811657 / 1250000000000 : ℝ))
      (E := (cell12800 ⟨16, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (8351836503761 / 10000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (27992811657 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_17 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (41741907909077 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239428915741 / 100000000000000 : ℝ))
      (E := (cell12800 ⟨17, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (41741907909077 / 50000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (2239428915741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_18 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83449290927871 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279929116699 / 12500000000000 : ℝ))
      (E := (cell12800 ⟨18, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83449290927871 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (279929116699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12800_19 : CellCertificate 12800 (441958914460239 / 5000000000000000 : ℝ) (82048338866219 / 50000000000000000 : ℝ) (331405528743167 / 10000000000000000 : ℝ)
    (cell12800 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · norm_num [cell12800]
  · have h := gap_lower (n := 12800) (a := (83414790333281 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119718466233 / 50000000000000 : ℝ))
      (E := (cell12800 ⟨19, by decide⟩).energy) (xi := (331405528743167 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12800 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12800]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12800])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12800) (a := (83414790333281 / 100000000000000 : ℝ)) (b := (160906982239 / 100000000000000 : ℝ)) (q := (1119718466233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12800])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12800]

theorem cert12801_0 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (525465465199 / 625000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239241372177 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨0, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (525465465199 / 625000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239241372177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_1 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (84039531563009 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111962268433 / 5000000000000 : ℝ))
      (E := (cell12801 ⟨1, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (84039531563009 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111962268433 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_2 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (84004613583029 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559812337699 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨2, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (84004613583029 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559812337699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_3 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83969720455499 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239253385153 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨3, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83969720455499 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239253385153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_4 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (5245928259013 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279907170549 / 12500000000000 : ℝ))
      (E := (cell12801 ⟨4, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (5245928259013 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279907170549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_5 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83900008613139 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239261354539 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨5, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83900008613139 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239261354539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_6 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83865189826459 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (447853072701 / 20000000000000 : ℝ))
      (E := (cell12801 ⟨6, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83865189826459 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (447853072701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_7 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (5239399734283 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119634699469 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨7, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (5239399734283 / 6250000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119634699469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_8 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83795626343889 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239273410231 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨8, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83795626343889 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239273410231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_9 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83760881577273 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111963870223 / 5000000000000 : ℝ))
      (E := (cell12801 ⟨9, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83760881577273 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111963870223 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_10 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83726161413593 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239281388451 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨10, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83726161413593 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239281388451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_11 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83691465817947 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111964268439 / 5000000000000 : ℝ))
      (E := (cell12801 ⟨11, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83691465817947 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (111964268439 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_12 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41828397377807 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (17914315279 / 800000000000 : ℝ))
      (E := (cell12801 ⟨12, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41828397377807 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (17914315279 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_13 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (41811074096027 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239293401637 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨13, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (41811074096027 / 50000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239293401637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_14 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16717505218581 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119648703989 / 50000000000000 : ℝ))
      (E := (cell12801 ⟨14, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16717505218581 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (1119648703989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_15 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83552928423987 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239301376313 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨15, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83552928423987 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239301376313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_16 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83518355151293 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559826357077 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨16, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83518355151293 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559826357077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_17 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16696761248199 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239309394477 / 100000000000000 : ℝ))
      (E := (cell12801 ⟨17, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16696761248199 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (2239309394477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_18 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (83449281659439 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279914174503 / 12500000000000 : ℝ))
      (E := (cell12801 ⟨18, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (83449281659439 / 100000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (279914174503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12801_19 : CellCertificate 12801 (35355612468009 / 400000000000000 : ℝ) (25638102265537 / 15625000000000000 : ℝ) (165689509335903 / 5000000000000000 : ℝ)
    (cell12801 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · norm_num [cell12801]
  · have h := gap_lower (n := 12801) (a := (16682956274629 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559829359391 / 25000000000000 : ℝ))
      (E := (cell12801 ⟨19, by decide⟩).energy) (xi := (165689509335903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12801 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12801]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12801])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12801) (a := (16682956274629 / 20000000000000 : ℝ)) (b := (160894261597 / 100000000000000 : ℝ)) (q := (559829359391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12801])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12801]

theorem cert12802_0 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (42037229770919 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (69972558921 / 3125000000000 : ℝ))
      (E := (cell12802 ⟨0, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (42037229770919 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (69972558921 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_1 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (42019758494581 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559781477813 / 25000000000000 : ℝ))
      (E := (cell12802 ⟨1, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (42019758494581 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559781477813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_2 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (84004599324891 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559782480863 / 25000000000000 : ℝ))
      (E := (cell12802 ⟨2, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (84004599324891 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559782480863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_3 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83969706512623 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111956693643 / 5000000000000 : ℝ))
      (E := (cell12802 ⟨3, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83969706512623 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (111956693643 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_4 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83934838516151 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239137883649 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨4, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83934838516151 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239137883649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_5 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16779999059891 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447828381223 / 20000000000000 : ℝ))
      (E := (cell12802 ⟨5, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16779999059891 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447828381223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_6 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83865176826707 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (11195729451 / 500000000000 : ℝ))
      (E := (cell12802 ⟨6, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83865176826707 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (11195729451 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_7 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16766076612453 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239149901471 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨7, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16766076612453 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239149901471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_8 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41897806985337 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119576944659 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨8, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41897806985337 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119576944659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_9 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41880434758333 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239157918847 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨9, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41880434758333 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239157918847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_10 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (16745229933031 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119580969449 / 50000000000000 : ℝ))
      (E := (cell12802 ⟨10, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (16745229933031 / 20000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (1119580969449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_11 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (2092286359531 / 2500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223916589797 / 10000000000000 : ℝ))
      (E := (cell12802 ⟨11, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (2092286359531 / 2500000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223916589797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_12 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83656783630201 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239169918519 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨12, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83656783630201 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239169918519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_13 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41811068688749 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (139948368153 / 6250000000000 : ℝ))
      (E := (cell12802 ⟨13, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41811068688749 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (139948368153 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_14 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (20896878897193 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239177935813 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨14, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (20896878897193 / 25000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239177935813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_15 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83552918229841 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223918194393 / 10000000000000 : ℝ))
      (E := (cell12802 ⟨15, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83552918229841 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (223918194393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_16 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83518345266701 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239185920071 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨16, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83518345266701 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239185920071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_17 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (3339351866621 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447837985497 / 20000000000000 : ℝ))
      (E := (cell12802 ⟨17, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (3339351866621 / 4000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (447837985497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_18 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (41724636196329 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559798478197 / 25000000000000 : ℝ))
      (E := (cell12802 ⟨18, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (41724636196329 / 50000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (559798478197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12802_19 : CellCertificate 12802 (883862798604379 / 10000000000000000 : ℝ) (82035516635203 / 50000000000000000 : ℝ) (331352512891803 / 10000000000000000 : ℝ)
    (cell12802 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · norm_num [cell12802]
  · have h := gap_lower (n := 12802) (a := (83414772414623 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239197938791 / 100000000000000 : ℝ))
      (E := (cell12802 ⟨19, by decide⟩).energy) (xi := (331352512891803 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12802 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12802]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12802])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12802) (a := (83414772414623 / 100000000000000 : ℝ)) (b := (160881542979 / 100000000000000 : ℝ)) (q := (2239197938791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12802])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12802]

theorem cert12803_0 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16814888930833 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119501225993 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨0, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16814888930833 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119501225993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_1 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (84039502417607 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (3498447577 / 156250000000 : ℝ))
      (E := (cell12803 ⟨1, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (84039502417607 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (3498447577 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_2 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16800917013801 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119505216859 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨2, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16800917013801 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119505216859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_3 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41984846285981 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279876808983 / 12500000000000 : ℝ))
      (E := (cell12803 ⟨3, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41984846285981 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279876808983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_4 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (8393482489027 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279877307047 / 12500000000000 : ℝ))
      (E := (cell12803 ⟨4, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (8393482489027 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279877307047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_5 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (8389998198791 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239022453283 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨5, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (8389998198791 / 10000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239022453283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_6 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16773032765811 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239026470489 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨6, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16773032765811 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239026470489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_7 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (5239398148629 / 6250000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (111951522883 / 5000000000000 : ℝ))
      (E := (cell12803 ⟨7, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (5239398148629 / 6250000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (111951522883 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_8 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (20948900399871 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223903448013 / 10000000000000 : ℝ))
      (E := (cell12803 ⟨8, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (20948900399871 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (223903448013 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_9 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83760857458047 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559759621753 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨9, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83760857458047 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559759621753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_10 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (20931534479667 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239042485131 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨10, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (20931534479667 / 25000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239042485131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_11 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41845721473223 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119523240531 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨11, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41845721473223 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119523240531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_12 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83656772506663 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279881310141 / 12500000000000 : ℝ))
      (E := (cell12803 ⟨12, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83656772506663 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (279881310141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_13 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83622126564781 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (139940905713 / 6250000000000 : ℝ))
      (E := (cell12803 ⟨13, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83622126564781 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (139940905713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_14 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83587505086439 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559764614897 / 25000000000000 : ℝ))
      (E := (cell12803 ⟨14, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83587505086439 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (559764614897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_15 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41776454018729 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239062449353 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨15, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41776454018729 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239062449353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_16 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (16703667076767 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119533233023 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨16, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (16703667076767 / 20000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119533233023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_17 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83483787091743 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239070456547 / 100000000000000 : ℝ))
      (E := (cell12803 ⟨17, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83483787091743 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (2239070456547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_18 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (83449263127529 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119537241943 / 50000000000000 : ℝ))
      (E := (cell12803 ⟨18, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (83449263127529 / 100000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (1119537241943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12803_19 : CellCertificate 12803 (27619852800999 / 312500000000000 : ℝ) (820291070224379 / 500000000000000000 : ℝ) (331326011402037 / 10000000000000000 : ℝ)
    (cell12803 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · norm_num [cell12803]
  · have h := gap_lower (n := 12803) (a := (41707381728857 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447815698883 / 20000000000000 : ℝ))
      (E := (cell12803 ⟨19, by decide⟩).energy) (xi := (331326011402037 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12803 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12803]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12803])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12803) (a := (41707381728857 / 50000000000000 : ℝ)) (b := (10054301649 / 6250000000000 : ℝ)) (q := (447815698883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12803])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12803]

theorem cert12804_0 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (84074429768821 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238883013899 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨0, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (84074429768821 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238883013899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_1 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (84039487848341 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (139930440037 / 6250000000000 : ℝ))
      (E := (cell12804 ⟨1, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (84039487848341 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (139930440037 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_2 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (21001142703843 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447778211039 / 20000000000000 : ℝ))
      (E := (cell12804 ⟨2, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (21001142703843 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447778211039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_3 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (20992419658379 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559723752123 / 25000000000000 : ℝ))
      (E := (cell12804 ⟨3, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (20992419658379 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559723752123 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_4 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16786962253313 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119449512329 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨4, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16786962253313 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119449512329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_5 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (10487496084813 / 12500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238903053983 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨5, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (10487496084813 / 12500000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238903053983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_6 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (2620785963547 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238907046411 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨6, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (2620785963547 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238907046411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_7 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (83830357695927 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (27986387619 / 1250000000000 : ℝ))
      (E := (cell12804 ⟨7, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (83830357695927 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (27986387619 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_8 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (1047444865379 / 1250000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559728766663 / 25000000000000 : ℝ))
      (E := (cell12804 ⟨8, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (1047444865379 / 1250000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559728766663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_9 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16752169080283 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238919050927 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨9, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16752169080283 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238919050927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_10 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (8372612617413 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (139932689197 / 6250000000000 : ℝ))
      (E := (cell12804 ⟨10, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (8372612617413 / 10000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (139932689197 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_11 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (20922857878391 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (111946352999 / 5000000000000 : ℝ))
      (E := (cell12804 ⟨11, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (20922857878391 / 25000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (111946352999 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_12 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16731352277 / 20000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238931039601 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨12, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16731352277 / 20000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238931039601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_13 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (836221157539 / 1000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559733757537 / 25000000000000 : ℝ))
      (E := (cell12804 ⟨13, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (836221157539 / 1000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (559733757537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_14 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (16717498917181 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238939037453 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨14, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (16717498917181 / 20000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238939037453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_15 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41776448923419 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119471533549 / 50000000000000 : ℝ))
      (E := (cell12804 ⟨15, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41776448923419 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (1119471533549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_16 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (41759162751347 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238947066233 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨16, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (41759162751347 / 50000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238947066233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_17 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (2608868047489 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447790207977 / 20000000000000 : ℝ))
      (E := (cell12804 ⟨17, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (2608868047489 / 3125000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (447790207977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_18 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (83449253864049 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238955051081 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨18, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (83449253864049 / 100000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238955051081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12804_19 : CellCertificate 12804 (883807784782021 / 10000000000000000 : ℝ) (820226984111883 / 500000000000000000 : ℝ) (331299514201383 / 10000000000000000 : ℝ)
    (cell12804 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · norm_num [cell12804]
  · have h := gap_lower (n := 12804) (a := (4170737725121 / 5000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238959046171 / 100000000000000 : ℝ))
      (E := (cell12804 ⟨19, by decide⟩).energy) (xi := (331299514201383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12804 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12804]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12804])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12804) (a := (4170737725121 / 5000000000000 : ℝ)) (b := (160856111811 / 100000000000000 : ℝ)) (q := (2238959046171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12804])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12804]

theorem cert12805_0 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (21018603721451 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119381814517 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨0, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (21018603721451 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119381814517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_1 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16807894656273 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238767627343 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨1, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16807894656273 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238767627343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_2 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (84004556563991 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238771614283 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨2, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (84004556563991 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238771614283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_3 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83969664697283 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (111938782821 / 5000000000000 : ℝ))
      (E := (cell12805 ⟨3, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83969664697283 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (111938782821 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_4 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (20983699411259 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238779646411 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨4, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (20983699411259 / 25000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238779646411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_5 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16779991074247 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238783650279 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨5, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16779991074247 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238783650279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_6 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83865137840053 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238787617967 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨6, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83865137840053 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238787617967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_7 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83830345015851 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238791673023 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨7, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83830345015851 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238791673023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_8 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83795576863179 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119397824443 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨8, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83795576863179 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119397824443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_9 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (8376083334677 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238799668623 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨9, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (8376083334677 / 10000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238799668623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_10 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83726114431541 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238803623017 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨10, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83726114431541 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238803623017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_11 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41845710041297 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89552305389 / 4000000000000 : ℝ))
      (E := (cell12805 ⟨11, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41845710041297 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89552305389 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_12 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83656750265211 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119405826021 / 50000000000000 : ℝ))
      (E := (cell12805 ⟨12, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83656750265211 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (1119405826021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_13 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (16724420988971 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238815681043 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨13, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (16724420988971 / 20000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238815681043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_14 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83587484087171 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (69963114669 / 3125000000000 : ℝ))
      (E := (cell12805 ⟨14, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83587484087171 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (69963114669 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_15 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83552887657979 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89552947233 / 4000000000000 : ℝ))
      (E := (cell12805 ⟨15, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83552887657979 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89552947233 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_16 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83518315623277 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (55970691561 / 2500000000000 : ℝ))
      (E := (cell12805 ⟨16, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83518315623277 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (55970691561 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_17 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (83483767949241 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238831677497 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨17, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (83483767949241 / 100000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238831677497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_18 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (4172462230111 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238835672611 / 100000000000000 : ℝ))
      (E := (cell12805 ⟨18, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (4172462230111 / 5000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (2238835672611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12805_19 : CellCertificate 12805 (883780284053567 / 10000000000000000 : ℝ) (205040727003049 / 125000000000000000 : ℝ) (331273021288721 / 10000000000000000 : ℝ)
    (cell12805 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · norm_num [cell12805]
  · have h := gap_lower (n := 12805) (a := (41707372774369 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89553586093 / 4000000000000 : ℝ))
      (E := (cell12805 ⟨19, by decide⟩).energy) (xi := (331273021288721 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12805 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12805]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12805])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12805) (a := (41707372774369 / 50000000000000 : ℝ)) (b := (8042169963 / 5000000000000 : ℝ)) (q := (89553586093 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12805])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12805]

theorem cert12806_0 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16814880001023 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (223864429739 / 10000000000000 : ℝ))
      (E := (cell12806 ⟨0, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16814880001023 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (223864429739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_1 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (84039458716679 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238648267377 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨1, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (84039458716679 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238648267377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_2 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (4200227115743 / 5000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119326142293 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨2, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (4200227115743 / 5000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119326142293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_3 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83969650763263 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238656299867 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨3, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83969650763263 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238656299867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_4 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41967392012841 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (55966506593 / 2500000000000 : ℝ))
      (E := (cell12806 ⟨4, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41967392012841 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (55966506593 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_5 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83899942066103 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559666075027 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨5, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83899942066103 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559666075027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_6 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83865124848701 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (55966707527 / 2500000000000 : ℝ))
      (E := (cell12806 ⟨6, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83865124848701 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (55966707527 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_7 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41915166168919 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238672274213 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨7, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41915166168919 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238672274213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_8 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83795564498063 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238676284839 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨8, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83795564498063 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238676284839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_9 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83760821294111 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238680282069 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨9, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83760821294111 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238680282069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_10 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83726102690901 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (89547370909 / 4000000000000 : ℝ))
      (E := (cell12806 ⟨10, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83726102690901 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (89547370909 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_11 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (41845704326767 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447737664291 / 20000000000000 : ℝ))
      (E := (cell12806 ⟨11, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (41845704326767 / 50000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (447737664291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_12 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16731347829459 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (44773846369 / 2000000000000 : ℝ))
      (E := (cell12806 ⟨12, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16731347829459 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (44773846369 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_13 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83622094137647 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559674067429 / 25000000000000 : ℝ))
      (E := (cell12806 ⟨13, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83622094137647 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (559674067429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_14 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16717494718047 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238700297307 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨14, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16717494718047 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238700297307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_15 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83552877470881 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238704290533 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨15, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83552877470881 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238704290533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_16 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (16703661149117 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (111935415643 / 5000000000000 : ℝ))
      (E := (cell12806 ⟨16, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (16703661149117 / 20000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (111935415643 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_17 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83483758380521 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238712311167 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨17, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83483758380521 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238712311167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_18 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83449235342041 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238716290237 / 100000000000000 : ℝ))
      (E := (cell12806 ⟨18, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83449235342041 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (2238716290237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12806_19 : CellCertificate 12806 (883752787445633 / 10000000000000000 : ℝ) (1640197683845941 / 1000000000000000000 : ℝ) (20702908291433 / 625000000000000 : ℝ)
    (cell12806 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · norm_num [cell12806]
  · have h := gap_lower (n := 12806) (a := (83414736596669 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119360156439 / 50000000000000 : ℝ))
      (E := (cell12806 ⟨19, by decide⟩).energy) (xi := (20702908291433 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12806 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12806]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12806])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12806) (a := (83414736596669 / 100000000000000 : ℝ)) (b := (160830688731 / 100000000000000 : ℝ)) (q := (1119360156439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12806])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12806]

theorem cert12807_0 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (84074385126753 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559631240287 / 25000000000000 : ℝ))
      (E := (cell12807 ⟨0, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (84074385126753 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (559631240287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_1 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (84039444154281 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119264480349 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨1, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (84039444154281 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119264480349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_2 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (84004528067981 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (69954154699 / 3125000000000 : ℝ))
      (E := (cell12807 ⟨2, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (84004528067981 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (69954154699 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_3 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (2624051150983 / 3125000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139908558677 / 6250000000000 : ℝ))
      (E := (cell12807 ⟨3, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (2624051150983 / 3125000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139908558677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_4 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83934770408503 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119270467251 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨4, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83934770408503 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119270467251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_5 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83899928763109 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119272472767 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨5, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83899928763109 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119272472767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_6 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (10483138982431 / 12500000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238548979829 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨6, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (10483138982431 / 12500000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238548979829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_7 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16766063932377 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238552929063 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨7, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16766063932377 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238552929063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_8 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (8379555213497 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119278487257 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨8, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (8379555213497 / 10000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119278487257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_9 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41880404621719 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238560949299 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨9, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41880404621719 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238560949299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_10 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (5232880684513 / 6250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238564976279 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨10, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (5232880684513 / 6250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238564976279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_11 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16738279445277 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139910559121 / 6250000000000 : ℝ))
      (E := (cell12807 ⟨11, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16738279445277 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139910559121 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_12 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20914182007813 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119286490363 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨12, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20914182007813 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119286490363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_13 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (3344883333291 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139911060659 / 6250000000000 : ℝ))
      (E := (cell12807 ⟨13, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (3344883333291 / 4000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (139911060659 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_14 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (41793731547549 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238580979297 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨14, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (41793731547549 / 50000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238580979297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_15 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (16710573457109 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447716990879 / 20000000000000 : ℝ))
      (E := (cell12807 ⟨15, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (16710573457109 / 20000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447716990879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_16 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (5219893491851 / 6250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119294479651 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨16, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (5219893491851 / 6250000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119294479651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_17 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83483748813487 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447718599823 / 20000000000000 : ℝ))
      (E := (cell12807 ⟨17, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83483748813487 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (447718599823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_18 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (83449226083511 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238596962201 / 100000000000000 : ℝ))
      (E := (cell12807 ⟨18, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (83449226083511 / 100000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (2238596962201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12807_19 : CellCertificate 12807 (3534901179829 / 40000000000000 : ℝ) (820034785841861 / 500000000000000000 : ℝ) (165610024161441 / 5000000000000000 : ℝ)
    (cell12807 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · norm_num [cell12807]
  · have h := gap_lower (n := 12807) (a := (20853681911553 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119300484783 / 50000000000000 : ℝ))
      (E := (cell12807 ⟨19, by decide⟩).energy) (xi := (165610024161441 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12807 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12807]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12807])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12807) (a := (20853681911553 / 25000000000000 : ℝ)) (b := (160817980223 / 100000000000000 : ℝ)) (q := (1119300484783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12807])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12807]

theorem cert12808_0 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (84074370250717 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238405620311 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨0, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (84074370250717 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238405620311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_1 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (21009857398543 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238409649461 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨1, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (21009857398543 / 25000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238409649461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_2 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (84004513823351 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119206834751 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨2, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (84004513823351 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119206834751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_3 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83969622901861 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (223841763121 / 10000000000000 : ℝ))
      (E := (cell12808 ⟨3, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83969622901861 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (223841763121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_4 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41967378396749 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238421658759 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨4, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41967378396749 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238421658759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_5 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (335599661849 / 400000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238425644497 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨5, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (335599661849 / 400000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238425644497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_6 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41932549436147 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447685930843 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨6, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41932549436147 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447685930843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_7 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83830306987993 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119216818787 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨7, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83830306987993 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119216818787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_8 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (837955397739 / 1000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (8743897109 / 390625000000 : ℝ))
      (E := (cell12808 ⟨8, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (837955397739 / 1000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (8743897109 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_9 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (335043188779 / 400000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447688334063 / 20000000000000 : ℝ))
      (E := (cell12808 ⟨9, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (335043188779 / 400000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (447688334063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_10 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (10465759901933 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (3581513081 / 160000000000 : ℝ))
      (E := (cell12808 ⟨10, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (10465759901933 / 12500000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (3581513081 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_11 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41845692900573 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559612420601 / 25000000000000 : ℝ))
      (E := (cell12808 ⟨11, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41845692900573 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (559612420601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_12 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41828358458541 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238453638871 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨12, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41828358458541 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238453638871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_13 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83622072528737 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119228833641 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨13, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83622072528737 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119228833641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_14 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41793726300879 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119230828617 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨14, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41793726300879 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119230828617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_15 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (83552857101969 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238465672413 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨15, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (83552857101969 / 100000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238465672413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_16 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (8351828599537 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119234829981 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨16, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (8351828599537 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119234829981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_17 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (4174186962407 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119236841561 / 50000000000000 : ℝ))
      (E := (cell12808 ⟨17, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (4174186962407 / 5000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (1119236841561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_18 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (8344921682663 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238477688507 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨18, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (8344921682663 / 10000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238477688507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12808_19 : CellCertificate 12808 (883697806587447 / 10000000000000000 : ℝ) (819970739766523 / 500000000000000000 : ℝ) (41399196033433 / 1250000000000000 : ℝ)
    (cell12808 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · norm_num [cell12808]
  · have h := gap_lower (n := 12808) (a := (41707359348683 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238481680657 / 100000000000000 : ℝ))
      (E := (cell12808 ⟨19, by decide⟩).energy) (xi := (41399196033433 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12808 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12808]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12808])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12808) (a := (41707359348683 / 50000000000000 : ℝ)) (b := (32161054747 / 20000000000000 : ℝ)) (q := (2238481680657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12808])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12808]

theorem cert12809_0 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (84074355377007 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238286390521 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨0, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (84074355377007 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238286390521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_1 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (1680788300727 / 2000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238290391513 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨1, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (1680788300727 / 2000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238290391513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_2 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (84004499580971 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119147192059 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨2, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (84004499580971 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119147192059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_3 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83969608974477 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119149188501 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨3, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83969608974477 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119149188501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_4 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83934743180667 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238302378577 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨4, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83934743180667 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238302378577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_5 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (10487487770441 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238306396997 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨5, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (10487487770441 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238306396997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_6 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83865085887237 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119155191101 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨6, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83865085887237 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119155191101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_7 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (41915147158081 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238314399747 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨7, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (41915147158081 / 50000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238314399747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_8 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (20948881853713 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238318399019 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨8, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (20948881853713 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238318399019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_9 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83760785148047 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559580596771 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨9, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83760785148047 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559580596771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_10 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83726067480667 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559581592691 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨10, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83726067480667 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559581592691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_11 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83691374377817 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238330414703 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨11, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83691374377817 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238330414703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_12 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (5228544112799 / 6250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (223833440909 / 10000000000000 : ℝ))
      (E := (cell12809 ⟨12, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (5228544112799 / 6250000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (223833440909 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_13 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (16724412345407 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238338418051 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨13, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (16724412345407 / 20000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238338418051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_14 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (10448430263777 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119171194633 / 50000000000000 : ℝ))
      (E := (cell12809 ⟨14, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (10448430263777 / 12500000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (1119171194633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_15 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83552846920153 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139896649151 / 6250000000000 : ℝ))
      (E := (cell12809 ⟨15, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83552846920153 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (139896649151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_16 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83518276122847 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (55958760371 / 2500000000000 : ℝ))
      (E := (cell12809 ⟨16, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83518276122847 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (55958760371 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_17 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83483729684477 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238354421411 / 100000000000000 : ℝ))
      (E := (cell12809 ⟨17, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83483729684477 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (2238354421411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_18 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (83449207571397 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (69948700341 / 3125000000000 : ℝ))
      (E := (cell12809 ⟨18, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (83449207571397 / 100000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (69948700341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12809_19 : CellCertificate 12809 (883670322335253 / 10000000000000000 : ℝ) (204976675923653 / 125000000000000000 : ℝ) (331167092495553 / 10000000000000000 : ℝ)
    (cell12809 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · norm_num [cell12809]
  · have h := gap_lower (n := 12809) (a := (20853677437533 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559590596971 / 25000000000000 : ℝ))
      (E := (cell12809 ⟨19, by decide⟩).energy) (xi := (331167092495553 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12809 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12809]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12809])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12809) (a := (20853677437533 / 25000000000000 : ℝ)) (b := (160792569267 / 100000000000000 : ℝ)) (q := (559590596971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12809])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12809]

theorem cert12810_0 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (84074340505621 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447633419663 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨0, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (84074340505621 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447633419663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_1 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (16807880096163 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (223817112901 / 10000000000000 : ℝ))
      (E := (cell12810 ⟨1, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (16807880096163 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (223817112901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_2 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (2100112133521 / 2500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447635030417 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨2, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (2100112133521 / 2500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447635030417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_3 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (16793919009861 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559544779579 / 25000000000000 : ℝ))
      (E := (cell12810 ⟨3, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (16793919009861 / 20000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (559544779579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_4 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83934729570009 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238183151871 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨4, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83934729570009 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238183151871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_5 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (4194994443347 / 5000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238187145099 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨5, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (4194994443347 / 5000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238187145099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_6 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41932536452139 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238191105827 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨6, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41932536452139 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238191105827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_7 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (8383028164639 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119097578799 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨7, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (8383028164639 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119097578799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_8 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83795515057827 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238199133849 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨8, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83795515057827 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238199133849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_9 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (2617524159479 / 3125000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238203157641 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨9, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (2617524159479 / 3125000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238203157641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_10 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (10465756968477 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (279775889969 / 12500000000000 : ℝ))
      (E := (cell12810 ⟨10, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (10465756968477 / 12500000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (279775889969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_11 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83691362956397 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447642228567 / 20000000000000 : ℝ))
      (E := (cell12810 ⟨11, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83691362956397 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (447642228567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_12 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41828347347179 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238215175179 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨12, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41828347347179 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238215175179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_13 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (41811025463583 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238219164731 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨13, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (41811025463583 / 50000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238219164731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_14 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83587431620471 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238223175393 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨14, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83587431620471 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238223175393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_15 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (81594567129 / 97656250000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238227154577 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨15, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (81594567129 / 97656250000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238227154577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_16 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83518266252047 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (111911558287 / 5000000000000 : ℝ))
      (E := (cell12810 ⟨16, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83518266252047 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (111911558287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_17 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (83483720122501 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (27977939447 / 1250000000000 : ℝ))
      (E := (cell12810 ⟨17, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (83483720122501 / 100000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (27977939447 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_18 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (20862299579453 / 25000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238239187659 / 100000000000000 : ℝ))
      (E := (cell12810 ⟨18, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (20862299579453 / 25000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (2238239187659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12810_19 : CellCertificate 12810 (883642842199699 / 10000000000000000 : ℝ) (102480334702973 / 62500000000000000 : ℝ) (331140621006029 / 10000000000000000 : ℝ)
    (cell12810 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · norm_num [cell12810]
  · have h := gap_lower (n := 12810) (a := (8341470080451 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119121574757 / 50000000000000 : ℝ))
      (E := (cell12810 ⟨19, by decide⟩).energy) (xi := (331140621006029 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12810 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12810]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12810])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12810) (a := (8341470080451 / 10000000000000 : ℝ)) (b := (160779866819 / 100000000000000 : ℝ)) (q := (1119121574757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12810])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12810]

theorem cert12811_0 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (84074325636561 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238047917159 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨0, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (84074325636561 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238047917159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_1 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (42019692963783 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238051919799 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨1, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (42019692963783 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238051919799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_2 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (42002235551479 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119027957769 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨2, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (42002235551479 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119027957769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_3 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83969581126343 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447611982609 / 20000000000000 : ℝ))
      (E := (cell12811 ⟨3, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83969581126343 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (447611982609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_4 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83934715961523 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279757990091 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨4, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83934715961523 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279757990091 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_5 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (10487484446561 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (111903397337 / 5000000000000 : ℝ))
      (E := (cell12811 ⟨5, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (10487484446561 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (111903397337 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_6 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (10483132490427 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279758992627 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨6, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (10483132490427 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279758992627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_7 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83830268978677 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279759488891 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨7, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83830268978677 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279759488891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_8 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41897751351411 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238079922407 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨8, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41897751351411 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238079922407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_9 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83760761060593 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119041961977 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨9, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83760761060593 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119041961977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_10 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (5232877751057 / 6250000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238087922589 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨10, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (5232877751057 / 6250000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238087922589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_11 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41845675768443 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119045962439 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨11, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41845675768443 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119045962439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_12 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83656683585803 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (111904796857 / 5000000000000 : ℝ))
      (E := (cell12811 ⟨12, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83656683585803 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (111904796857 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_13 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (20905510032283 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (55952497683 / 2500000000000 : ℝ))
      (E := (cell12811 ⟨13, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (20905510032283 / 25000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (55952497683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_14 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (41793710566261 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (223810395747 / 10000000000000 : ℝ))
      (E := (cell12811 ⟨14, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (41793710566261 / 50000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (223810395747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_15 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83552826561799 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559526979681 / 25000000000000 : ℝ))
      (E := (cell12811 ⟨15, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83552826561799 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (559526979681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_16 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (10439782047871 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119055985431 / 50000000000000 : ℝ))
      (E := (cell12811 ⟨16, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (10439782047871 / 12500000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (1119055985431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_17 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (2608865955069 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279764493049 / 12500000000000 : ℝ))
      (E := (cell12811 ⟨17, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (2608865955069 / 3125000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (279764493049 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_18 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (667593512527 / 800000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238119960507 / 100000000000000 : ℝ))
      (E := (cell12811 ⟨18, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (667593512527 / 800000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (2238119960507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12811_19 : CellCertificate 12811 (110451920772477 / 1250000000000000 : ℝ) (327911464620679 / 200000000000000000 : ℝ) (82778538449443 / 2500000000000000 : ℝ)
    (cell12811 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · norm_num [cell12811]
  · have h := gap_lower (n := 12811) (a := (83414691860497 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (44762479311 / 2000000000000 : ℝ))
      (E := (cell12811 ⟨19, by decide⟩).energy) (xi := (82778538449443 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12811 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12811]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12811])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12811) (a := (83414691860497 / 100000000000000 : ℝ)) (b := (16076716639 / 10000000000000 : ℝ)) (q := (44762479311 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12811])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12811]

theorem cert12812_0 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (3362972430793 / 4000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237928731411 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨0, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (3362972430793 / 4000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237928731411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_1 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (21009842844151 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118966353017 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨1, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (21009842844151 / 25000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118966353017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_2 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (84004456867323 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118968366173 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨2, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (84004456867323 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118968366173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_3 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83969567205591 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (22379407033 / 1000000000000 : ℝ))
      (E := (cell12812 ⟨3, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83969567205591 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (22379407033 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_4 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83934702355209 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447588948613 / 20000000000000 : ℝ))
      (E := (cell12812 ⟨4, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83934702355209 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447588948613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_5 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83899862280169 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447589748797 / 20000000000000 : ℝ))
      (E := (cell12812 ⟨5, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83899862280169 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447589748797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_6 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83865046944651 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447590542777 / 20000000000000 : ℝ))
      (E := (cell12812 ⟨6, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83865046944651 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447590542777 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_7 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41915128156511 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118978359163 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨7, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41915128156511 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118978359163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_8 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83795490349839 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559490191173 / 25000000000000 : ℝ))
      (E := (cell12812 ⟨8, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83795490349839 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559490191173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_9 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41880374509921 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237964744057 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨9, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41880374509921 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237964744057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_10 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (41863016143977 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237968721223 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨10, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (41863016143977 / 50000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237968721223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_11 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83691340119283 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447594552167 / 20000000000000 : ℝ))
      (E := (cell12812 ⟨11, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83691340119283 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (447594552167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_12 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83656672479119 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559494188269 / 25000000000000 : ℝ))
      (E := (cell12812 ⟨12, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83656672479119 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (559494188269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_13 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83622029332931 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (279747595259 / 12500000000000 : ℝ))
      (E := (cell12812 ⟨13, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83622029332931 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (279747595259 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_14 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83587410646369 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237984735497 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨14, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83587410646369 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237984735497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_15 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83552816385261 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237988737031 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨15, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83552816385261 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237988737031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_16 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83518246515611 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237992772011 / 100000000000000 : ℝ))
      (E := (cell12812 ⟨16, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83518246515611 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (2237992772011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_17 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (83483701003601 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118998393653 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨17, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (83483701003601 / 100000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1118998393653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_18 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (16689835963117 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (22380007877 / 1000000000000 : ℝ))
      (E := (cell12812 ⟨18, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (16689835963117 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (22380007877 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12812_19 : CellCertificate 12812 (883587894274633 / 10000000000000000 : ℝ) (819714655476009 / 500000000000000000 : ℝ) (66217538173933 / 2000000000000000 : ℝ)
    (cell12812 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · norm_num [cell12812]
  · have h := gap_lower (n := 12812) (a := (16682936583619 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119002388863 / 50000000000000 : ℝ))
      (E := (cell12812 ⟨19, by decide⟩).energy) (xi := (66217538173933 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12812 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12812]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12812])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12812) (a := (16682936583619 / 20000000000000 : ℝ)) (b := (160754467979 / 100000000000000 : ℝ)) (q := (1119002388863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12812])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12812]

theorem cert12813_0 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (21018573976353 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118904799447 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨0, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (21018573976353 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118904799447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_1 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (84039356827927 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118906772781 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨1, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (84039356827927 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118906772781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_2 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (5250277664621 / 6250000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237817602509 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨2, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (5250277664621 / 6250000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237817602509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_3 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83969553287049 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2185372661 / 97656250000 : ℝ))
      (E := (cell12813 ⟨3, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83969553287049 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2185372661 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_4 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83934688751067 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118912780483 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨4, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83934688751067 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118912780483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_5 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (2621870280937 / 3125000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237829594771 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨5, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (2621870280937 / 3125000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237829594771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_6 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83865033967981 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237833598321 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨6, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83865033967981 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237833598321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_7 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83830243649427 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237837579187 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨7, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83830243649427 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237837579187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_8 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83795477998877 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447568320539 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨8, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83795477998877 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447568320539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_9 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83760736981073 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118922779959 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨9, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83760736981073 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118922779959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_10 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (4186301028047 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (223784957371 / 10000000000000 : ℝ))
      (E := (cell12813 ⟨10, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (4186301028047 / 5000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (223784957371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_11 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20922832175897 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237853592627 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨11, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20922832175897 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237853592627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_12 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (16731332274861 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559464405747 / 25000000000000 : ℝ))
      (E := (cell12813 ⟨12, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (16731332274861 / 20000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (559464405747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_13 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83622018538563 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447572322547 / 20000000000000 : ℝ))
      (E := (cell12813 ⟨13, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83622018538563 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (447572322547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_14 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (20896850040503 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (223786562577 / 10000000000000 : ℝ))
      (E := (cell12813 ⟨14, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (20896850040503 / 25000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (223786562577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_15 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83552806210481 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237869609499 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨15, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83552806210481 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237869609499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_16 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (3340729465999 / 4000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237873627381 / 100000000000000 : ℝ))
      (E := (cell12813 ⟨16, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (3340729465999 / 4000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (2237873627381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_17 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83483691446677 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118938813143 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨17, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83483691446677 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118938813143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_18 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83449170566943 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118940805497 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨18, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83449170566943 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118940805497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12813_19 : CellCertificate 12813 (441780213241591 / 5000000000000000 : ℝ) (1639301318788757 / 1000000000000000000 : ℝ) (82765308055147 / 2500000000000000 : ℝ)
    (cell12813 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · norm_num [cell12813]
  · have h := gap_lower (n := 12813) (a := (83414673977303 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118942793021 / 50000000000000 : ℝ))
      (E := (cell12813 ⟨19, by decide⟩).energy) (xi := (82765308055147 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12813 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12813]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12813])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12813) (a := (83414673977303 / 100000000000000 : ℝ)) (b := (160741771587 / 100000000000000 : ℝ)) (q := (1118942793021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12813])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12813]

theorem cert12814_0 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (42037140521661 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237690461789 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨0, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (42037140521661 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237690461789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_1 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16807868456307 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118847219193 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨1, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16807868456307 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118847219193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_2 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (21001107100699 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237698468161 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨2, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (21001107100699 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237698468161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_3 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (16793907874143 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118851222033 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨3, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (16793907874143 / 20000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118851222033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_4 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83934675149097 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237706432349 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨4, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83934675149097 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237706432349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_5 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83899835701933 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237710441163 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨5, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83899835701933 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237710441163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_6 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83865020993407 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237714478401 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨6, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83865020993407 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237714478401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_7 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (5239389436743 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237718435733 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨7, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (5239389436743 / 6250000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237718435733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_8 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41897732824967 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118861218211 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨8, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41897732824967 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118861218211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_9 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83760724944287 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237726487603 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨9, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83760724944287 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237726487603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_10 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (2616437776121 / 3125000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237730480051 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨10, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (2616437776121 / 3125000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237730480051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_11 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (418456586449 / 500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (4370575153 / 195312500000 : ℝ))
      (E := (cell12814 ⟨11, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (418456586449 / 500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (4370575153 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_12 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83656650271361 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279717311097 / 12500000000000 : ℝ))
      (E := (cell12814 ⟨12, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83656650271361 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (279717311097 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_13 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (20905501936507 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237742459313 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨13, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (20905501936507 / 25000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237742459313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_14 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (1671747793589 / 2000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237746453849 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨14, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (1671747793589 / 2000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237746453849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_15 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83552796037459 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118875238979 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨15, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83552796037459 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118875238979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_16 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (4175911339303 / 5000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (111887723939 / 5000000000000 : ℝ))
      (E := (cell12814 ⟨16, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (4175911339303 / 5000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (111887723939 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_17 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (83483681891437 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237758461333 / 100000000000000 : ℝ))
      (E := (cell12814 ⟨17, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (83483681891437 / 100000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (2237758461333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_18 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (41724580659973 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118881244319 / 50000000000000 : ℝ))
      (E := (cell12814 ⟨18, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (41724580659973 / 50000000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (1118881244319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12814_19 : CellCertificate 12814 (176706592560899 / 2000000000000000 : ℝ) (1639173346608929 / 1000000000000000000 : ℝ) (20689673615589 / 625000000000000 : ℝ)
    (cell12814 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · norm_num [cell12814]
  · have h := gap_lower (n := 12814) (a := (2085366625953 / 2500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447553301407 / 20000000000000 : ℝ))
      (E := (cell12814 ⟨19, by decide⟩).energy) (xi := (20689673615589 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12814 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12814]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12814])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12814) (a := (2085366625953 / 2500000000000 : ℝ)) (b := (160729077211 / 100000000000000 : ℝ)) (q := (447553301407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12814])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12814]

theorem cert12815_0 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16814853236711 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559392844479 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨0, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16814853236711 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559392844479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_1 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (21009831934357 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111878766333 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨1, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (21009831934357 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111878766333 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_2 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (42002207086951 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237579329303 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨2, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (42002207086951 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237579329303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_3 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (8396952545659 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118791668343 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨3, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (8396952545659 / 10000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118791668343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_4 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (5245916346831 / 6250000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447517471443 / 20000000000000 : ℝ))
      (E := (cell12815 ⟨4, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (5245916346831 / 6250000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447517471443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_5 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41949911208007 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (22375913411 / 1000000000000 : ℝ))
      (E := (cell12815 ⟨5, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41949911208007 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (22375913411 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_6 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83865008020927 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237595354127 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨6, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83865008020927 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237595354127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_7 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83830218328407 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559399836487 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨7, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83830218328407 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559399836487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_8 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83795453303011 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (17481276421 / 781250000000 : ℝ))
      (E := (cell12815 ⟨8, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83795453303011 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (17481276421 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_9 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41880356454741 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118803676509 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨9, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41880356454741 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118803676509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_10 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20931499278187 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237611382191 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨10, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20931499278187 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237611382191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_11 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83691305877919 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118807679941 / 50000000000000 : ℝ))
      (E := (cell12815 ⟨11, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83691305877919 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (1118807679941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_12 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83656639170287 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237619350439 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨12, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83656639170287 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237619350439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_13 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20905499238831 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237623359931 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨13, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20905499238831 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237623359931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_14 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (83587379198683 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (17481464017 / 781250000000 : ℝ))
      (E := (cell12815 ⟨14, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (83587379198683 / 100000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (17481464017 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_15 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41776392933097 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111881570029 / 5000000000000 : ℝ))
      (E := (cell12815 ⟨15, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41776392933097 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (111881570029 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_16 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (16703643384773 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559408846101 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨16, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (16703643384773 / 20000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559408846101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_17 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (2087091808447 / 2500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559409852221 / 25000000000000 : ℝ))
      (E := (cell12815 ⟨17, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (2087091808447 / 2500000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (559409852221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_18 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (20862288018649 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447528672477 / 20000000000000 : ℝ))
      (E := (cell12815 ⟨18, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (20862288018649 / 25000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (447528672477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12815_19 : CellCertificate 12815 (441752751618801 / 5000000000000000 : ℝ) (327809078881571 / 200000000000000000 : ℝ) (66201665551011 / 2000000000000000 : ℝ)
    (cell12815 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · norm_num [cell12815]
  · have h := gap_lower (n := 12815) (a := (41707328050273 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237647365903 / 100000000000000 : ℝ))
      (E := (cell12815 ⟨19, by decide⟩).energy) (xi := (66201665551011 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12815 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12815]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12815])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12815) (a := (41707328050273 / 50000000000000 : ℝ)) (b := (160716384853 / 100000000000000 : ℝ)) (q := (2237647365903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12815])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12815]

theorem cert12816_0 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (84074251326109 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (139840768091 / 6250000000000 : ℝ))
      (E := (cell12816 ⟨0, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (84074251326109 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (139840768091 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_1 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (21009828298901 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237456268231 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨1, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (21009828298901 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237456268231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_2 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (42002199973627 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279682537709 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨2, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (42002199973627 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279682537709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_3 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83969511544673 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279683035341 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨3, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83969511544673 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279683035341 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_4 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41967323975833 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237468277649 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨4, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41967323975833 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237468277649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_5 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (20974952283057 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118736147291 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨5, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (20974952283057 / 25000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118736147291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_6 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83864995050543 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118738141729 / 50000000000000 : ℝ))
      (E := (cell12816 ⟨6, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83864995050543 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (1118738141729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_7 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83830205670983 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237480309831 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨7, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83830205670983 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237480309831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_8 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83795440958107 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237484323077 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨8, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83795440958107 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237484323077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_9 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (4188035043833 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (89499530889 / 4000000000000 : ℝ))
      (E := (cell12816 ⟨9, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (4188035043833 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (89499530889 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_10 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83725985391569 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237492280129 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨10, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83725985391569 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237492280129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_11 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (16738258893589 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447499259069 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨11, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (16738258893589 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447499259069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_12 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (41828314035541 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279687540523 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨12, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (41828314035541 / 50000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279687540523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_13 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83621986166453 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559376078647 / 25000000000000 : ℝ))
      (E := (cell12816 ⟨13, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83621986166453 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559376078647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_14 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83587368719711 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237508330457 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨14, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83587368719711 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237508330457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_15 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83552775696687 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237512319193 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨15, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83552775696687 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237512319193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_16 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (8351820706339 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237516344253 / 100000000000000 : ℝ))
      (E := (cell12816 ⟨16, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (8351820706339 / 10000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (2237516344253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_17 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (16696732557201 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447504058857 / 20000000000000 : ℝ))
      (E := (cell12816 ⟨17, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (16696732557201 / 20000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (447504058857 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_18 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (83449142830891 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559381087181 / 25000000000000 : ℝ))
      (E := (cell12816 ⟨18, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (83449142830891 / 100000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (559381087181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12816_19 : CellCertificate 12816 (883478047781537 / 10000000000000000 : ℝ) (819458731090429 / 500000000000000000 : ℝ) (66196376387273 / 2000000000000000 : ℝ)
    (cell12816 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · norm_num [cell12816]
  · have h := gap_lower (n := 12816) (a := (4170732358229 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279691042181 / 12500000000000 : ℝ))
      (E := (cell12816 ⟨19, by decide⟩).energy) (xi := (66196376387273 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12816 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12816]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12816])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12816) (a := (4170732358229 / 5000000000000 : ℝ)) (b := (10043980907 / 6250000000000 : ℝ)) (q := (279691042181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12816])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12816]

theorem cert12817_0 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16814847294197 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237333254233 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨0, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16814847294197 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237333254233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_1 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (1313114041501 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (22373372631 / 1000000000000 : ℝ))
      (E := (cell12817 ⟨1, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (1313114041501 / 1562500000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (22373372631 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_2 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (21001096430713 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118670634767 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨2, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (21001096430713 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118670634767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_3 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20992374408741 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118672612151 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨3, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20992374408741 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118672612151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_4 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16786926871241 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237349251569 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨4, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16786926871241 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237349251569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_5 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83899795850573 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118676621837 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨5, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83899795850573 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118676621837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_6 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20966245520563 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237357266401 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨6, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20966245520563 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237357266401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_7 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16766038603123 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118680634701 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨7, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16766038603123 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118680634701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_8 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41897714307611 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237365259991 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨8, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41897714307611 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237365259991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_9 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (41880344422909 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237369245229 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨9, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (41880344422909 / 50000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237369245229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_10 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20931493418083 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (4369869707 / 195312500000 : ℝ))
      (E := (cell12817 ⟨10, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20931493418083 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (4369869707 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_11 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20922820764969 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237377284729 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨11, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20922820764969 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237377284729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_12 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16731323394749 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237381293809 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨12, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16731323394749 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237381293809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_13 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20905493844853 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447477053033 / 20000000000000 : ℝ))
      (E := (cell12817 ⟨13, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20905493844853 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447477053033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_14 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (20896839560633 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447477852539 / 20000000000000 : ℝ))
      (E := (cell12817 ⟨14, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (20896839560633 / 25000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (447477852539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_15 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (10444095691117 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237393291973 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨15, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (10444095691117 / 12500000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237393291973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_16 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (16703639440927 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118698650067 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨16, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (16703639440927 / 20000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118698650067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_17 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83483653235813 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118700646097 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨17, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83483653235813 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118700646097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_18 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83449133588831 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237405272929 / 100000000000000 : ℝ))
      (E := (cell12817 ⟨18, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83449133588831 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (2237405272929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12817_19 : CellCertificate 12817 (88345059643533 / 1000000000000000 : ℝ) (1638789549923259 / 1000000000000000000 : ℝ) (330955440392237 / 10000000000000000 : ℝ)
    (cell12817 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · norm_num [cell12817]
  · have h := gap_lower (n := 12817) (a := (83414638230223 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118704652569 / 50000000000000 : ℝ))
      (E := (cell12817 ⟨19, by decide⟩).energy) (xi := (330955440392237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12817 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12817]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12817])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12817) (a := (83414638230223 / 100000000000000 : ℝ)) (b := (80345503093 / 50000000000000 : ℝ)) (q := (1118704652569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12817])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12817]

theorem cert12818_0 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (42037110809091 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279651776803 / 12500000000000 : ℝ))
      (E := (cell12818 ⟨0, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (42037110809091 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279651776803 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_1 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (42019642059403 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89488730137 / 4000000000000 : ℝ))
      (E := (cell12818 ⟨1, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (42019642059403 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89488730137 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_2 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (42002185750347 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237222232889 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨2, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (42002185750347 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237222232889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_3 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83969483727461 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237226219299 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨3, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83969483727461 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237226219299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_4 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41967310381457 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237230221059 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨4, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41967310381457 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237230221059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_5 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83899782571049 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118617123157 / 50000000000000 : ℝ))
      (E := (cell12818 ⟨5, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83899782571049 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (1118617123157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_6 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41932484558027 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237238244993 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨6, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41932484558027 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237238244993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_7 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83830180362303 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237242224659 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨7, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83830180362303 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237242224659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_8 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (16759083254871 / 20000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237246250639 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨8, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (16759083254871 / 20000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237246250639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_9 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83760676816957 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237250272029 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨9, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83760676816957 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237250272029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_10 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83725961955039 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237254237583 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨10, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83725961955039 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237254237583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_11 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41845635826857 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (8739290117 / 390625000000 : ℝ))
      (E := (cell12818 ⟨11, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41845635826857 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (8739290117 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_12 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (20914151469569 / 25000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (139828891207 / 6250000000000 : ℝ))
      (E := (cell12818 ⟨12, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (20914151469569 / 25000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (139828891207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_13 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41810982297101 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279658283723 / 12500000000000 : ℝ))
      (E := (cell12818 ⟨13, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41810982297101 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (279658283723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_14 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41793673883573 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237270249037 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨14, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41793673883573 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237270249037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_15 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83552755362941 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237274260747 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨15, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83552755362941 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237274260747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_16 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (41759093673799 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237278252047 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨16, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (41759093673799 / 50000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237278252047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_17 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83483643687303 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237282286173 / 100000000000000 : ℝ))
      (E := (cell12818 ⟨17, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83483643687303 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (2237282286173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_18 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (162986570993 / 195312500000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559321562871 / 25000000000000 : ℝ))
      (E := (cell12818 ⟨18, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (162986570993 / 195312500000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (559321562871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12818_19 : CellCertificate 12818 (13803486706219 / 156250000000000 : ℝ) (102416353601899 / 62500000000000000 : ℝ) (66185800624311 / 2000000000000000 : ℝ)
    (cell12818 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · norm_num [cell12818]
  · have h := gap_lower (n := 12818) (a := (83414629297473 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89491610759 / 4000000000000 : ℝ))
      (E := (cell12818 ⟨19, by decide⟩).energy) (xi := (66185800624311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12818 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12818]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12818])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12818) (a := (83414629297473 / 100000000000000 : ℝ)) (b := (40169579969 / 25000000000000 : ℝ)) (q := (89491610759 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12818])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12818]

theorem cert12819_0 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (84074206767699 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447419045571 / 20000000000000 : ℝ))
      (E := (cell12819 ⟨0, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (84074206767699 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447419045571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_1 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (84039269583831 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447419847841 / 20000000000000 : ℝ))
      (E := (cell12819 ⟨1, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (84039269583831 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447419847841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_2 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (84004357280781 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237103249607 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨2, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (84004357280781 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237103249607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_3 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (20992367455541 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559276816931 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨3, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (20992367455541 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559276816931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_4 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (8393460717179 / 10000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237111244039 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨4, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (8393460717179 / 10000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237111244039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_5 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10487471161707 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118557622283 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨5, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10487471161707 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118557622283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_6 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (1677299123039 / 2000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559279819299 / 25000000000000 : ℝ))
      (E := (cell12819 ⟨6, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (1677299123039 / 2000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (559279819299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_7 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (16766033542209 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237123291579 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨7, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (16766033542209 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237123291579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_8 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (16759080787101 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (89485091801 / 4000000000000 : ℝ))
      (E := (cell12819 ⟨8, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (16759080787101 / 20000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (89485091801 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_9 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (20940166197519 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447426258919 / 20000000000000 : ℝ))
      (E := (cell12819 ⟨9, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (20940166197519 / 25000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (447426258919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_10 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (10465743779961 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (22371352971 / 1000000000000 : ℝ))
      (E := (cell12819 ⟨10, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (10465743779961 / 12500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (22371352971 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_11 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (5230703765591 / 6250000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237139251019 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨11, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (5230703765591 / 6250000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237139251019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_12 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (3346263791387 / 4000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (5592858197 / 250000000000 : ℝ))
      (E := (cell12819 ⟨12, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (3346263791387 / 4000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (5592858197 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_13 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83621953810823 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237147270323 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨13, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83621953810823 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237147270323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_14 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41793668646777 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118575644743 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨14, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41793668646777 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118575644743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_15 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83552745198703 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237155283689 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨15, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83552745198703 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237155283689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_16 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (2087954437307 / 2500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237159316387 / 100000000000000 : ℝ))
      (E := (cell12819 ⟨16, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (2087954437307 / 2500000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (2237159316387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_17 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41741817070237 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (89486531049 / 4000000000000 : ℝ))
      (E := (cell12819 ⟨17, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41741817070237 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (89486531049 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_18 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (41724557554823 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (279645910549 / 12500000000000 : ℝ))
      (E := (cell12819 ⟨18, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (41724557554823 / 50000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (279645910549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12819_19 : CellCertificate 12819 (441697853034313 / 5000000000000000 : ℝ) (40963344632439 / 25000000000000000 : ℝ) (66180514024641 / 2000000000000000 : ℝ)
    (cell12819 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · norm_num [cell12819]
  · have h := gap_lower (n := 12819) (a := (83414620366331 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118585643613 / 50000000000000 : ℝ))
      (E := (cell12819 ⟨19, by decide⟩).energy) (xi := (66180514024641 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12819 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12819]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12819])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12819) (a := (83414620366331 / 100000000000000 : ℝ)) (b := (8033281779 / 5000000000000 : ℝ)) (q := (1118585643613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12819])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12819]

theorem cert12820_0 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (5254636994971 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559244073631 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨0, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (5254636994971 / 6250000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559244073631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_1 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (84039255051137 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118490139143 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨1, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (84039255051137 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118490139143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_2 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (84004343063111 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223698431969 / 10000000000000 : ℝ))
      (E := (cell12820 ⟨2, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (84004343063111 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223698431969 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_3 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41984727959537 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (3495294237 / 156250000000 : ℝ))
      (E := (cell12820 ⟨3, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41984727959537 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (3495294237 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_4 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (16786918716567 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447398464101 / 20000000000000 : ℝ))
      (E := (cell12820 ⟨4, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (16786918716567 / 20000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (447398464101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_5 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41949878009197 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2236996296367 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨5, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41949878009197 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2236996296367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_6 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41932471594969 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279625038131 / 12500000000000 : ℝ))
      (E := (cell12820 ⟨6, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41932471594969 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (279625038131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_7 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83830155061843 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118502148099 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨7, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83830155061843 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118502148099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_8 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83795391598673 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (69906510473 / 3125000000000 : ℝ))
      (E := (cell12820 ⟨8, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83795391598673 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (69906510473 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_9 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41880326382587 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118506156463 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨9, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41880326382587 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118506156463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_10 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83725938526279 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559254073591 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨10, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83725938526279 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559254073591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_11 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83691248847103 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118510172043 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨11, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83691248847103 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118510172043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_12 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41828291846471 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237024352269 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨12, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41828291846471 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237024352269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_13 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83621943029273 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118514162453 / 50000000000000 : ℝ))
      (E := (cell12820 ⟨13, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83621943029273 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (1118514162453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_14 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41793663410877 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559258081473 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨14, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41793663410877 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559258081473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_15 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83552735036219 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2796295451 / 125000000000 : ℝ))
      (E := (cell12820 ⟨15, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83552735036219 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2796295451 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_16 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (2087954190967 / 2500000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559260079641 / 25000000000000 : ℝ))
      (E := (cell12820 ⟨16, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (2087954190967 / 2500000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (559260079641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_17 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (41741812297663 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237044320567 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨17, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (41741812297663 / 50000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237044320567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_18 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (83449105872519 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237048371653 / 100000000000000 : ℝ))
      (E := (cell12820 ⟨18, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (83449105872519 / 100000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (2237048371653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12820_19 : CellCertificate 12820 (441684133523097 / 5000000000000000 : ℝ) (1638405932920113 / 1000000000000000000 : ℝ) (33087614139607 / 1000000000000000 : ℝ)
    (cell12820 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · norm_num [cell12820]
  · have h := gap_lower (n := 12820) (a := (20853652859199 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223705235989 / 10000000000000 : ℝ))
      (E := (cell12820 ⟨19, by decide⟩).energy) (xi := (33087614139607 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12820 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12820]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12820])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12820) (a := (20853652859199 / 25000000000000 : ℝ)) (b := (1606529533 / 1000000000000 : ℝ)) (q := (223705235989 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12820])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12820]

theorem cert12821_0 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (21018544268423 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236857356613 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨0, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (21018544268423 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236857356613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_1 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (3361569620829 / 4000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236861370671 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨1, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (3361569620829 / 4000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236861370671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_2 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (21001082211921 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (223686538527 / 10000000000000 : ℝ))
      (E := (cell12821 ⟨2, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (21001082211921 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (223686538527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_3 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83969442018189 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118434704533 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨3, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83969442018189 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118434704533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_4 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83934579996047 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236873392547 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨4, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83934579996047 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236873392547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_5 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83899742745261 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236877401721 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨5, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83899742745261 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236877401721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_6 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41932465115009 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559220346629 / 25000000000000 : ℝ))
      (E := (cell12821 ⟨6, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41932465115009 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (559220346629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_7 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (16766028482939 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118442706241 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨7, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (16766028482939 / 20000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118442706241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_8 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83795379263857 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236889370977 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨8, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83795379263857 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236889370977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_9 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83760640742251 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236893385059 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨9, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83760640742251 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236893385059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_10 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20931481703703 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118448701773 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨10, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20931481703703 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118448701773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_11 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41845618723327 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236901374919 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨11, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41845618723327 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236901374919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_12 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (3346262904123 / 4000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236905421623 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨12, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (3346262904123 / 4000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236905421623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_13 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83621932249553 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118454716769 / 50000000000000 : ℝ))
      (E := (cell12821 ⟨13, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83621932249553 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (1118454716769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_14 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41793658175873 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236913416409 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨14, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41793658175873 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236913416409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_15 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (8355272487549 / 10000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236917433909 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨15, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (8355272487549 / 10000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236917433909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_16 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (41759078893399 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236921433169 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨16, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (41759078893399 / 50000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236921433169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_17 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83483615051859 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236925419203 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨17, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83483615051859 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236925419203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_18 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (20862274159259 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236929396783 / 100000000000000 : ℝ))
      (E := (cell12821 ⟨18, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (20862274159259 / 25000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (2236929396783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12821_19 : CellCertificate 12821 (883340832129753 / 10000000000000000 : ℝ) (1638278100493373 / 1000000000000000000 : ℝ) (82712429234759 / 2500000000000000 : ℝ)
    (cell12821 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · norm_num [cell12821]
  · have h := gap_lower (n := 12821) (a := (83414602508867 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447386685741 / 20000000000000 : ℝ))
      (E := (cell12821 ⟨19, by decide⟩).energy) (xi := (82712429234759 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12821 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12821]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12821])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12821) (a := (83414602508867 / 100000000000000 : ℝ)) (b := (160640273033 / 100000000000000 : ℝ)) (q := (447386685741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12821])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12821]

theorem cert12822_0 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (84074162230167 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236738471943 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨0, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (84074162230167 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236738471943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_1 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (84039225992593 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (55918562909 / 2500000000000 : ℝ))
      (E := (cell12822 ⟨1, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (84039225992593 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (55918562909 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_2 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (84004314634501 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447349300843 / 20000000000000 : ℝ))
      (E := (cell12822 ⟨2, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (84004314634501 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447349300843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_3 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20992357029877 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236750501989 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨3, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20992357029877 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236750501989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_4 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41967283205713 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (6989857869 / 312500000000 : ℝ))
      (E := (cell12822 ⟨4, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41967283205713 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (6989857869 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_5 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83899729474257 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236758502689 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨5, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83899729474257 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236758502689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_6 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83864917272189 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (5460846 / 244140625 : ℝ))
      (E := (cell12822 ⟨6, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83864917272189 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (5460846 / 244140625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_7 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83830129769601 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279595815557 / 12500000000000 : ℝ))
      (E := (cell12822 ⟨7, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83830129769601 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (279595815557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_8 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83795366931057 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236770518567 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨8, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83795366931057 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236770518567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_9 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83760628721307 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139798406937 / 6250000000000 : ℝ))
      (E := (cell12822 ⟨9, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83760628721307 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (139798406937 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_10 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41862957552643 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447355701707 / 20000000000000 : ℝ))
      (E := (cell12822 ⟨10, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41862957552643 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447355701707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_11 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20922806512027 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236782517757 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨11, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20922806512027 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236782517757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_12 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41828280757537 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (111839324343 / 5000000000000 : ℝ))
      (E := (cell12822 ⟨12, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41828280757537 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (111839324343 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_13 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (41810960735831 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236790538091 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨13, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (41810960735831 / 50000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236790538091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_14 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (8358730588353 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559198625721 / 25000000000000 : ℝ))
      (E := (cell12822 ⟨14, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (8358730588353 / 10000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (559198625721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_15 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20888178679129 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447359700603 / 20000000000000 : ℝ))
      (E := (cell12822 ⟨15, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20888178679129 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (447359700603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_16 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (83518147936633 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236802543811 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨16, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (83518147936633 / 100000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236802543811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_17 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (10435450688759 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236806513913 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨17, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (10435450688759 / 12500000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236806513913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_18 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (20862271850799 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236810534511 / 100000000000000 : ℝ))
      (E := (cell12822 ⟨18, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (20862271850799 / 25000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (2236810534511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12822_19 : CellCertificate 12822 (441656700659169 / 5000000000000000 : ℝ) (163815028801267 / 100000000000000000 : ℝ) (33082329675099 / 1000000000000000 : ℝ)
    (cell12822 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · norm_num [cell12822]
  · have h := gap_lower (n := 12822) (a := (16682918716509 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (17475113687 / 781250000000 : ℝ))
      (E := (cell12822 ⟨19, by decide⟩).energy) (xi := (33082329675099 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12822 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12822]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12822])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12822) (a := (16682918716509 / 20000000000000 : ℝ)) (b := (8031379739 / 5000000000000 : ℝ)) (q := (17475113687 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12822])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12822]

theorem cert12823_0 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (84074147388959 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118309820259 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨0, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (84074147388959 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118309820259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_1 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (42019605733371 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236623599663 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨1, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (42019605733371 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236623599663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_2 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (84004300423559 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (111831380933 / 5000000000000 : ℝ))
      (E := (cell12823 ⟨2, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (84004300423559 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (111831380933 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_3 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (10496176777879 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236631648341 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨3, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (10496176777879 / 12500000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236631648341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_4 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20983638207243 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236635639189 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨4, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20983638207243 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236635639189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_5 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83899716205381 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236639657213 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨5, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83899716205381 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236639657213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_6 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83864904316451 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236643652337 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨6, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83864904316451 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236643652337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_7 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (523938232041 / 625000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236647632123 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨7, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (523938232041 / 625000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236647632123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_8 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83795354600273 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236651661889 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨8, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83795354600273 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236651661889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_9 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41880308351171 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118327816347 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨9, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41880308351171 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118327816347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_10 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (837259033977 / 1000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236659667389 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨10, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (837259033977 / 1000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236659667389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_11 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41845607325733 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (55916591411 / 2500000000000 : ℝ))
      (E := (cell12823 ⟨11, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41845607325733 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (55916591411 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_12 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83656550428939 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559166916047 / 25000000000000 : ℝ))
      (E := (cell12823 ⟨12, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83656550428939 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (559166916047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_13 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83621910695599 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236671638567 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨13, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83621910695599 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236671638567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_14 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (16717459083421 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236675643471 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨14, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (16717459083421 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236675643471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_15 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (1305511008739 / 1562500000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118339813147 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨15, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (1305511008739 / 1562500000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118339813147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_16 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (41759069044093 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236683650489 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨16, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (41759069044093 / 50000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236683650489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_17 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (16696719193993 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236687662919 / 100000000000000 : ℝ))
      (E := (cell12823 ⟨17, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (16696719193993 / 20000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (2236687662919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_18 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (83449078170999 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (17474153659 / 781250000000 : ℝ))
      (E := (cell12823 ⟨18, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (83449078170999 / 100000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (17474153659 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12823_19 : CellCertificate 12823 (441642987305491 / 5000000000000000 : ℝ) (204752811934167 / 125000000000000000 : ℝ) (165398440415409 / 5000000000000000 : ℝ)
    (cell12823 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · norm_num [cell12823]
  · have h := gap_lower (n := 12823) (a := (20853646164457 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118347835659 / 50000000000000 : ℝ))
      (E := (cell12823 ⟨19, by decide⟩).energy) (xi := (165398440415409 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12823 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12823]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12823])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12823) (a := (20853646164457 / 25000000000000 : ℝ)) (b := (8030745927 / 5000000000000 : ℝ)) (q := (1118347835659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12823])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12823]

theorem cert12824_0 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (8407413255007 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447300160903 / 20000000000000 : ℝ))
      (E := (cell12824 ⟨0, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (8407413255007 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (447300160903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_1 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (8403919694317 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (55912619853 / 2500000000000 : ℝ))
      (E := (cell12824 ⟨1, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (8403919694317 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (55912619853 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_2 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (84004286214859 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (89460351459 / 4000000000000 : ℝ))
      (E := (cell12824 ⟨2, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (84004286214859 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (89460351459 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_3 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83969400328759 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118256395117 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨3, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83969400328759 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118256395117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_4 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20983634812171 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (69891150431 / 3125000000000 : ℝ))
      (E := (cell12824 ⟨4, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20983634812171 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (69891150431 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_5 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41949851469317 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236520807353 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨5, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41949851469317 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236520807353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_6 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20966222840701 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236524778729 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨6, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20966222840701 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236524778729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_7 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20957526121393 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223652879347 / 10000000000000 : ℝ))
      (E := (cell12824 ⟨7, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20957526121393 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (223652879347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_8 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16759068454301 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236532800941 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨8, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16759068454301 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236532800941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_9 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41880302342677 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236536808201 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨9, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41880302342677 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236536808201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_10 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (16745178338411 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559135205513 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨10, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (16745178338411 / 20000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559135205513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_11 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83691203256727 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559136197743 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨11, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83691203256727 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559136197743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_12 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83656539344669 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236548837403 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨12, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83656539344669 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236548837403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_13 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20905474980341 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118276396547 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨13, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20905474980341 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118276396547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_14 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (10448410619059 / 12500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236556838169 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨14, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (10448410619059 / 12500000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236556838169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_15 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (8355269440383 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118280401873 / 50000000000000 : ℝ))
      (E := (cell12824 ⟨15, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (8355269440383 / 10000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (1118280401873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_16 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (41759064120727 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559141202851 / 25000000000000 : ℝ))
      (E := (cell12824 ⟨16, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (41759064120727 / 50000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (559141202851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_17 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83483586431537 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236568808001 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨17, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83483586431537 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236568808001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_18 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (20862267235111 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236572856553 / 100000000000000 : ℝ))
      (E := (cell12824 ⟨18, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (20862267235111 / 25000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (2236572856553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

theorem cert12824_19 : CellCertificate 12824 (2760182975021 / 31250000000000 : ℝ) (818947361435353 / 500000000000000000 : ℝ) (330770469177407 / 10000000000000000 : ℝ)
    (cell12824 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · norm_num [cell12824]
  · have h := gap_lower (n := 12824) (a := (83414575734717 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (6989302641 / 312500000000 : ℝ))
      (E := (cell12824 ⟨19, by decide⟩).energy) (xi := (330770469177407 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12824 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12824]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12824])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12824) (a := (83414575734717 / 100000000000000 : ℝ)) (b := (20075280539 / 12500000000000 : ℝ)) (q := (6989302641 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12824])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12824]

end BstLean.Part268
