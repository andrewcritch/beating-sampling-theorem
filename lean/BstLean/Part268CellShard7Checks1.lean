import BstLean.Part268CellShard7Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12525_20 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83382754647009 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284201144121 / 12500000000000 : ℝ))
      (E := (cell12525 ⟨20, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83382754647009 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284201144121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_21 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (5209263535449 / 6250000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227361318443 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨21, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (5209263535449 / 6250000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227361318443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_22 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (10414212850447 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273617183709 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨22, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (10414212850447 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273617183709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_23 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20819803330787 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273621154843 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨23, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20819803330787 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273621154843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_24 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41622374046517 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273625159983 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨24, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41622374046517 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273625159983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_25 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (10401288385067 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273629144383 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨25, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (10401288385067 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273629144383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_26 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (26616284881 / 32000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568408292443 / 25000000000000 : ℝ))
      (E := (cell12525 ⟨26, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (26616284881 / 32000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568408292443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_27 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83141497578437 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273637122463 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨27, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83141497578437 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273637122463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_28 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20776782256069 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (113682056107 / 5000000000000 : ℝ))
      (E := (cell12525 ⟨28, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20776782256069 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (113682056107 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_29 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (8307278455861 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273645171501 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨29, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (8307278455861 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273645171501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_30 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83038464149571 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273649156019 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨30, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83038464149571 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273649156019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_31 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41502083882727 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568413284077 / 25000000000000 : ℝ))
      (E := (cell12525 ⟨31, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41502083882727 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568413284077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_32 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20742473843679 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273657172843 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨32, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20742473843679 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273657172843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_33 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41467823472987 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227366115027 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨33, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41467823472987 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227366115027 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_34 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82901422448007 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136832564293 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨34, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82901422448007 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136832564293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_35 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (331468887399 / 400000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136834583827 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨35, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (331468887399 / 400000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136834583827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_36 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82833045120299 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136836575649 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨36, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82833045120299 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136836575649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_37 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41399446114453 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136838569453 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨37, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41399446114453 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136838569453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_38 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82764763144977 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273681131057 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨38, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82764763144977 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273681131057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_39 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (3309226313523 / 4000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136842564051 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨39, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (3309226313523 / 4000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136842564051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12526_20 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (1302855399149 / 1562500000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273479431973 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨20, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (1302855399149 / 1562500000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273479431973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_21 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83348207783619 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568370858499 / 25000000000000 : ℝ))
      (E := (cell12526 ⟨21, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83348207783619 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568370858499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_22 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (20828423584369 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142092966429 / 6250000000000 : ℝ))
      (E := (cell12526 ⟨22, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (20828423584369 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142092966429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_23 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (8327920517407 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (45469829287 / 2000000000000 : ℝ))
      (E := (cell12526 ⟨23, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (8327920517407 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (45469829287 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_24 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16648948052107 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273495442253 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨24, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16648948052107 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273495442253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_25 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (3328411982567 / 4000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142093716157 / 6250000000000 : ℝ))
      (E := (cell12526 ⟨25, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (3328411982567 / 4000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142093716157 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_26 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83175883052461 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273503458121 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨26, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83175883052461 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273503458121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_27 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (10392686336629 / 12500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (227350744417 / 10000000000000 : ℝ))
      (E := (cell12526 ⟨27, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (10392686336629 / 12500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (227350744417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_28 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (8310712245369 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (3552361593 / 156250000000 : ℝ))
      (E := (cell12526 ⟨28, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (8310712245369 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (3552361593 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_29 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16614555660481 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136757722633 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨29, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16614555660481 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136757722633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_30 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83038458207311 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136759703441 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨30, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83038458207311 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136759703441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_31 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41502081068351 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (4547046847 / 200000000000 : ℝ))
      (E := (cell12526 ⟨31, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41502081068351 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (4547046847 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_32 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82969890059037 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273527438579 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨32, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82969890059037 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273527438579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_33 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82935641942933 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273531453827 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨33, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82935641942933 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273531453827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_34 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82901417757171 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273535412129 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨34, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82901417757171 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273535412129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_35 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41433608735343 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136769715947 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨35, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41433608735343 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136769715947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_36 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (3313321642103 / 4000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136771727789 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨36, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (3313321642103 / 4000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136771727789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_37 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (8279888847209 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (56838685633 / 2500000000000 : ℝ))
      (E := (cell12526 ⟨37, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (8279888847209 / 10000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (56838685633 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_38 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82764759698639 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454710291799 / 20000000000000 : ℝ))
      (E := (cell12526 ⟨38, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82764759698639 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454710291799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_39 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41365327350893 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273555439609 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨39, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41365327350893 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273555439609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12527_20 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83382736445753 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273349765109 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨20, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83382736445753 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273349765109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_21 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41674099500853 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273353796041 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨21, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41674099500853 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273353796041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_22 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (20828421468247 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568339449069 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨22, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (20828421468247 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568339449069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_23 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16655839405313 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284170221231 / 12500000000000 : ℝ))
      (E := (cell12527 ⟨23, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16655839405313 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284170221231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_24 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83244732429571 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568341444727 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨24, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83244732429571 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568341444727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_25 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (8321029204931 / 10000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227336976871 / 10000000000000 : ℝ))
      (E := (cell12527 ⟨25, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (8321029204931 / 10000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227336976871 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_26 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16635175170651 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136686871289 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨26, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16635175170651 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136686871289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_27 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16628296761809 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273377762027 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨27, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16628296761809 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273377762027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_28 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83107115884483 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136690885769 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨28, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83107115884483 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136690885769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_29 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41536386023771 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568346443433 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨29, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41536386023771 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568346443433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_30 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83038452266353 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454677954201 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨30, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83038452266353 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454677954201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_31 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41502078254607 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136696882759 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨31, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41502078254607 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136696882759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_32 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82969884744583 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454679551841 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨32, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82969884744583 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454679551841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_33 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (2073390923527 / 2500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227340175377 / 10000000000000 : ℝ))
      (E := (cell12527 ⟨33, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (2073390923527 / 2500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227340175377 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_34 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82901413067483 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273405750689 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨34, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82901413067483 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273405750689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_35 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (20716803273183 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568352437803 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨35, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (20716803273183 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568352437803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_36 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82833036985923 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273413756361 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨36, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82833036985923 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273413756361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_37 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (20699721179077 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136708883469 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨37, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (20699721179077 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136708883469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_38 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82764756253297 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454684356703 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨38, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82764756253297 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454684356703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_39 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41365325783227 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136712873869 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨39, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41365325783227 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136712873869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12528_20 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41691363673831 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273220152377 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨20, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41691363673831 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273220152377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_21 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (16669638044289 / 20000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136612076999 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨21, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (16669638044289 / 20000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136612076999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_22 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41656838705057 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273228125639 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨22, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41656838705057 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273228125639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_23 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41639594440317 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273232129669 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨23, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41639594440317 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273232129669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_24 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41622362300071 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (45464723399 / 2000000000000 : ℝ))
      (E := (cell12528 ⟨24, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41622362300071 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (45464723399 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_25 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83210284535941 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273240133359 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨25, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83210284535941 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273240133359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_26 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41587934327753 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273244139951 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨26, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41587934327753 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273244139951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_27 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20785369231619 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273248134461 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨27, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20785369231619 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273248134461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_28 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5194194332291 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136626059873 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨28, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5194194332291 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136626059873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_29 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41536382897009 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136628078451 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨29, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41536382897009 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136628078451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_30 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83038446326697 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136630065699 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨30, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83038446326697 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136630065699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_31 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83004150882989 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273264162367 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨31, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83004150882989 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273264162367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_32 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41484939715677 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568317033681 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨32, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41484939715677 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568317033681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_33 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20733907985103 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454654433447 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨33, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20733907985103 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454654433447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_34 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (1295334505921 / 1562500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136638072133 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨34, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (1295334505921 / 1562500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136638072133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_35 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5179200544743 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273280125611 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨35, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5179200544743 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273280125611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_36 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41416516460171 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273284112289 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨36, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41416516460171 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273284112289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_37 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82798880961559 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136644081881 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨37, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82798880961559 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136644081881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_38 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (1655295056179 / 2000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454658432661 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨38, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (1655295056179 / 2000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454658432661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_39 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82730648432079 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273296169907 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨39, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82730648432079 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273296169907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12529_20 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (4169135912563 / 5000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273090593779 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨20, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (4169135912563 / 5000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273090593779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_21 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (16669636288567 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273094566151 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨21, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (16669636288567 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273094566151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_22 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83313668948851 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568274641893 / 25000000000000 : ℝ))
      (E := (cell12529 ⟨22, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83313668948851 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568274641893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_23 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20819795184069 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273102543813 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨23, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20819795184069 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273102543813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_24 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41622358386123 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (90924262281 / 4000000000000 : ℝ))
      (E := (cell12529 ⟨24, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41622358386123 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (90924262281 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_25 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83210277024067 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136555276229 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨25, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83210277024067 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136555276229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_26 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83175861459213 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273114591837 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨26, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83175861459213 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273114591837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_27 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20785367511331 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (35517477523 / 1562500000000 : ℝ))
      (E := (cell12529 ⟨27, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20785367511331 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (35517477523 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_28 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (162318560059 / 195312500000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273122581043 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨28, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (162318560059 / 195312500000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273122581043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_29 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20768189885459 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273126536301 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨29, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20768189885459 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273126536301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_30 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83038440388343 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273130546557 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨30, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83038440388343 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273130546557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_31 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83004145258027 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (90925382221 / 4000000000000 : ℝ))
      (E := (cell12529 ⟨31, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83004145258027 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (90925382221 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_32 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82969874119349 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454627713027 / 20000000000000 : ℝ))
      (E := (cell12529 ⟨32, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82969874119349 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454627713027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_33 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82935626940931 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (35517852767 / 1562500000000 : ℝ))
      (E := (cell12529 ⟨33, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82935626940931 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (35517852767 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_34 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (2590668865361 / 3125000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (17758957299 / 781250000000 : ℝ))
      (E := (cell12529 ⟨34, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (2590668865361 / 3125000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (17758957299 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_35 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82867204340153 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227315055509 / 10000000000000 : ℝ))
      (E := (cell12529 ⟨35, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82867204340153 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227315055509 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_36 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82833028855831 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273154581999 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨36, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82833028855831 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273154581999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_37 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82798877207843 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568289639283 / 25000000000000 : ℝ))
      (E := (cell12529 ⟨37, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82798877207843 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568289639283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_38 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82764749365597 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (14207265873 / 625000000000 : ℝ))
      (E := (cell12529 ⟨38, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82764749365597 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (14207265873 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_39 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82730645298661 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136583294349 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨39, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82730645298661 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136583294349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12530_20 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83382709156549 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454592206211 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨20, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83382709156549 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454592206211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_21 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20837043166469 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136482516251 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨21, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20837043166469 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136482516251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_22 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (208284151223 / 250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136484531883 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨22, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (208284151223 / 250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136484531883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_23 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83279172593491 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272973012283 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨23, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83279172593491 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272973012283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_24 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20811177236471 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568244264211 / 25000000000000 : ℝ))
      (E := (cell12530 ⟨24, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20811177236471 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568244264211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_25 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10401283689211 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227298102601 / 10000000000000 : ℝ))
      (E := (cell12530 ⟨25, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10401283689211 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227298102601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_26 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10396981783047 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136492519919 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨26, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10396981783047 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136492519919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_27 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (8314146316559 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136494521531 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨27, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (8314146316559 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136494521531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_28 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41553548092569 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454598607707 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨28, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41553548092569 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454598607707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_29 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (5192047080687 / 6250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (28412462861 / 1250000000000 : ℝ))
      (E := (cell12530 ⟨29, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (5192047080687 / 6250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (28412462861 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_30 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83038434451289 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136500508243 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨30, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83038434451289 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136500508243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_31 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10375517454291 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454601000703 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨31, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10375517454291 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454601000703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_32 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82969868808569 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (56825226261 / 2500000000000 : ℝ))
      (E := (cell12530 ⟨32, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82969868808569 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (56825226261 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_33 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (16587124388527 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (22730130419 / 1000000000000 : ℝ))
      (E := (cell12530 ⟨33, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (16587124388527 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (22730130419 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_34 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82901399005307 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273017037889 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨34, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82901399005307 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273017037889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_35 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82867199965527 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273021039653 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨35, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82867199965527 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273021039653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_36 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10354128099049 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284128131027 / 12500000000000 : ℝ))
      (E := (cell12530 ⟨36, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10354128099049 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284128131027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_37 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82798873455159 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273029005711 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨37, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82798873455159 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273029005711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_38 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82764745923239 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227303303001 / 10000000000000 : ℝ))
      (E := (cell12530 ⟨38, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82764745923239 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227303303001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_39 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82730642166199 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284129632853 / 12500000000000 : ℝ))
      (E := (cell12530 ⟨39, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82730642166199 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284129632853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12531_20 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83382700063527 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272831580727 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨20, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83382700063527 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272831580727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_21 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41674081945283 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136417776527 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨21, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41674081945283 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136417776527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_22 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83313652031161 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136419777957 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨22, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83313652031161 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136419777957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_23 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83279164452277 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (56821088377 / 2500000000000 : ℝ))
      (E := (cell12531 ⟨23, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83279164452277 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (56821088377 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_24 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (2601396910033 / 3125000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284105944087 / 12500000000000 : ℝ))
      (E := (cell12531 ⟨24, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (2601396910033 / 3125000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284105944087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_25 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83210262004803 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136425777007 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨25, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83210262004803 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136425777007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_26 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41587923535497 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454571108471 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨26, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41587923535497 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454571108471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_27 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83141456287273 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454571904161 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨27, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83141456287273 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454571904161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_28 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41553544810723 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272863550669 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨28, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41553544810723 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272863550669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_29 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83072747041489 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272867576163 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨29, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83072747041489 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272867576163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_30 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83038428515537 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272871541183 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨30, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83038428515537 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272871541183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_31 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83004134011891 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284109445607 / 12500000000000 : ℝ))
      (E := (cell12531 ⟨31, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83004134011891 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284109445607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_32 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82969863499013 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (35513742689 / 1562500000000 : ℝ))
      (E := (cell12531 ⟨32, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82969863499013 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (35513742689 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_33 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (3317424677821 / 4000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568220890417 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨33, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (3317424677821 / 4000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568220890417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_34 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (8290139432021 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454577507587 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨34, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (8290139432021 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454577507587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_35 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (8286719559201 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454578304137 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨35, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (8286719559201 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454578304137 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_36 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82833020730023 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272895569579 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨36, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82833020730023 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272895569579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_37 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20699717425877 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136449784079 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨37, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20699717425877 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136449784079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_38 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (132423587971 / 160000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272903575611 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨38, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (132423587971 / 160000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272903575611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_39 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82730639034693 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284113441697 / 12500000000000 : ℝ))
      (E := (cell12531 ⟨39, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82730639034693 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284113441697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12532_20 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83382690972193 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568175531569 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨20, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83382690972193 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568175531569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_21 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83348155116907 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136353063903 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨21, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83348155116907 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136353063903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_22 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20828410893683 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284088762791 / 12500000000000 : ℝ))
      (E := (cell12532 ⟨22, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20828410893683 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284088762791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_23 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20819789078159 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568178528051 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨23, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20819789078159 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568178528051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_24 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (520279333111 / 625000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272718102941 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨24, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (520279333111 / 625000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272718102941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_25 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20802563624353 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136361068237 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨25, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20802563624353 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136361068237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_26 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20793959969767 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227272609939 / 10000000000000 : ℝ))
      (E := (cell12532 ⟨26, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20793959969767 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227272609939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_27 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20785362352593 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568182527889 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨27, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20785362352593 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568182527889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_28 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20776770764783 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272734117447 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨28, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20776770764783 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272734117447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_29 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20768185198331 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136369059841 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨29, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20768185198331 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136369059841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_30 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (16607684516217 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272742120651 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨30, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (16607684516217 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272742120651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_31 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20751032097679 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272746122511 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨31, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20751032097679 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272746122511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_32 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (2074246454767 / 2500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272750127193 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨32, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (2074246454767 / 2500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272750127193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_33 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (103669514937 / 125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568188534099 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨33, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (103669514937 / 125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568188534099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_34 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82901389636259 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568189523251 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨34, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82901389636259 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568189523251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_35 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82867191219601 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272762115417 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨35, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82867191219601 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272762115417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_36 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (3313320666749 / 4000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272766087453 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨36, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (3313320666749 / 4000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272766087453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_37 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (10349858244111 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272770127157 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨37, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (10349858244111 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272770127157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_38 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (16552947808301 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272774117801 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨38, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (16552947808301 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272774117801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_39 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82730635904143 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272778118371 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨39, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82730635904143 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272778118371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12533_20 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83382681882549 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272572725963 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨20, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83382681882549 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272572725963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_21 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83348146344897 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568144174619 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨21, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83348146344897 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568144174619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_22 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83313635119913 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272580703007 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨22, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83313635119913 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272580703007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_23 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41639574087283 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136292371829 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨23, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41639574087283 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136292371829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_24 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83244685475997 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136294353789 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨24, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83244685475997 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136294353789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_25 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41605123495757 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272592715011 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨25, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41605123495757 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272592715011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_26 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20793958172149 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454519342189 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨26, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20793958172149 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454519342189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_27 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83141442534887 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272600698463 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨27, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83141442534887 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272600698463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_28 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20776769124549 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (227260473887 / 10000000000000 : ℝ))
      (E := (cell12533 ⟨28, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20776769124549 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (227260473887 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_29 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41536367273249 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272608717909 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨29, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41536367273249 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272608717909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_30 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83038416647933 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136306348197 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨30, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83038416647933 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136306348197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_31 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83004122770803 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272616735001 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨31, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83004122770803 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272616735001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_32 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (8296985288357 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454524143729 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨32, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (8296985288357 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454524143729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_33 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82935606954859 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272624707519 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨33, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82935606954859 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272624707519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_34 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (16580276990691 / 20000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284078587887 / 12500000000000 : ℝ))
      (E := (cell12533 ⟨34, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (16580276990691 / 20000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284078587887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_35 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (828671868483 / 1000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272632706621 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨35, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (828671868483 / 1000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272632706621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_36 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (5177063288031 / 6250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272636719113 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨36, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (5177063288031 / 6250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272636719113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_37 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82798862203301 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454528148273 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨37, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82798862203301 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454528148273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_38 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (5172795975133 / 6250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454528943053 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨38, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (5172795975133 / 6250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454528943053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_39 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20682658193637 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568162174949 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨39, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20682658193637 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568162174949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12534_20 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (2605708524831 / 3125000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227244337979 / 10000000000000 : ℝ))
      (E := (cell12534 ⟨20, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (2605708524831 / 3125000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227244337979 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_21 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (10418517196817 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272447381633 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨21, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (10418517196817 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272447381633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_22 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (5207101666669 / 6250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272451357953 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨22, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (5207101666669 / 6250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272451357953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_23 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83279140038067 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272455371109 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨23, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83279140038067 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272455371109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_24 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41622338827883 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (142028710413 / 6250000000000 : ℝ))
      (E := (cell12534 ⟨24, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41622338827883 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (142028710413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_25 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (8321023948711 / 10000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568115837001 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨25, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (8321023948711 / 10000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568115837001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_26 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83175825499579 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136233688509 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨26, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83175825499579 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136233688509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_27 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83141435660817 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113623569919 / 5000000000000 : ℝ))
      (E := (cell12534 ⟨27, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83141435660817 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113623569919 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_28 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (20776767484659 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272475356491 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨28, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (20776767484659 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272475356491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_29 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83072728301011 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454495874169 / 20000000000000 : ℝ))
      (E := (cell12534 ⟨29, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83072728301011 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454495874169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_30 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41519205358041 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454496677081 / 20000000000000 : ℝ))
      (E := (cell12534 ⟨30, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41519205358041 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454496677081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_31 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83004117152151 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272487343807 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨31, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83004117152151 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272487343807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_32 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82969847577683 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136245682497 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨32, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82969847577683 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136245682497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_33 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82935601961303 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272495392169 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨33, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82935601961303 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272495392169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_34 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82901380271797 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568124842053 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨34, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82901380271797 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568124842053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_35 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82867182478107 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272503352911 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨35, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82867182478107 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272503352911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_36 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82833008549337 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568126836821 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨36, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82833008549337 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568126836821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_37 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (10349857306843 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136255676063 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨37, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (10349857306843 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136255676063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_38 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (16552946432749 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568128842001 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨38, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (16552946432749 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568128842001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_39 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82730629645909 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (35508115551 / 1562500000000 : ℝ))
      (E := (cell12534 ⟨39, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82730629645909 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (35508115551 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12535_20 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83382663708323 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136157043879 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨20, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83382663708323 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136157043879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_21 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (1302314512591 / 1562500000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272318060711 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨21, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (1302314512591 / 1562500000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272318060711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_22 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (16662723643021 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (71010064599 / 3125000000000 : ℝ))
      (E := (cell12535 ⟨22, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (16662723643021 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (71010064599 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_23 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83279131903139 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272326052893 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨23, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83279131903139 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272326052893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_24 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41622334918533 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454466016007 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨24, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41622334918533 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454466016007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_25 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83210231984199 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568083523459 / 25000000000000 : ℝ))
      (E := (cell12535 ⟨25, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83210231984199 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568083523459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_26 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (5198488644501 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454467619523 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨26, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (5198488644501 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454467619523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_27 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83141428788163 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272342094457 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨27, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83141428788163 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272342094457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_28 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83107063380453 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227234608721 / 10000000000000 : ℝ))
      (E := (cell12535 ⟨28, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83107063380453 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227234608721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_29 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83072722056861 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454470015699 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨29, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83072722056861 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454470015699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_30 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83038404785529 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284044258837 / 12500000000000 : ℝ))
      (E := (cell12535 ⟨30, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83038404785529 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284044258837 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_31 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (2075102788369 / 2500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227235806597 / 10000000000000 : ℝ))
      (E := (cell12535 ⟨31, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (2075102788369 / 2500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227235806597 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_32 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41484921136509 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568090516561 / 25000000000000 : ℝ))
      (E := (cell12535 ⟨32, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41484921136509 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568090516561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_33 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82935596968931 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (17752859947 / 781250000000 : ℝ))
      (E := (cell12535 ⟨33, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82935596968931 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (17752859947 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_34 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (20725343897821 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136185044177 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨34, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (20725343897821 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136185044177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_35 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41433589054511 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227237405429 / 10000000000000 : ℝ))
      (E := (cell12535 ⟨35, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41433589054511 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227237405429 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_36 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82833004491247 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136189044623 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨36, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82833004491247 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136189044623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_37 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82798854707219 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272382076761 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨37, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82798854707219 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272382076761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_38 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (16552945745271 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272386076019 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨38, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (16552945745271 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272386076019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_39 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (5170664157389 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454478017473 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨39, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (5170664157389 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454478017473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12536_20 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83382654623741 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568046212467 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨20, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83382654623741 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568046212467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_21 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (2083703000969 / 2500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272188852279 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨21, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (2083703000969 / 2500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272188852279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_22 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (16662721953023 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (45443856613 / 2000000000000 : ℝ))
      (E := (cell12536 ⟨22, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (16662721953023 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (45443856613 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_23 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (4163956188489 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136098423671 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨23, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (4163956188489 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136098423671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_24 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41622331009949 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454440169571 / 20000000000000 : ℝ))
      (E := (cell12536 ⟨24, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41622331009949 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454440169571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_25 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (4160511224139 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136102417873 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨25, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (4160511224139 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136102417873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_26 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41587905562953 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227220881433 / 10000000000000 : ℝ))
      (E := (cell12536 ⟨26, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41587905562953 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227220881433 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_27 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20785355479231 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272212845117 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨27, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20785355479231 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272212845117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_28 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41553528411823 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272216814127 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨28, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41553528411823 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272216814127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_29 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83072715814049 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136110420427 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨29, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83072715814049 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136110420427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_30 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20759599714069 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272224810759 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨30, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20759599714069 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272224810759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_31 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83004105918629 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227222884297 / 10000000000000 : ℝ))
      (E := (cell12536 ⟨31, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83004105918629 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227222884297 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_32 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (10371229621197 / 12500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136116411197 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨32, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (10371229621197 / 12500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136116411197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_33 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82935591977743 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (284029601153 / 12500000000000 : ℝ))
      (E := (cell12536 ⟨33, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82935591977743 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (284029601153 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_34 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82901370911917 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272240804931 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨34, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82901370911917 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272240804931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_35 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82867173741043 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136122405379 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨35, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82867173741043 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136122405379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_36 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41416500217113 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (56806220693 / 2500000000000 : ℝ))
      (E := (cell12536 ⟨36, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41416500217113 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (56806220693 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_37 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (3311954038429 / 4000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568063199487 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨37, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (3311954038429 / 4000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568063199487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_38 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82764725289957 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227225683931 / 10000000000000 : ℝ))
      (E := (cell12536 ⟨38, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82764725289957 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227225683931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_39 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41365311695747 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568065208701 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨39, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41365311695747 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568065208701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12537_20 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41691322770423 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272055607861 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨20, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41691322770423 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272055607861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_21 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (651157119323 / 781250000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272059639769 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨21, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (651157119323 / 781250000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272059639769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_22 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41656800658367 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142003974381 / 6250000000000 : ℝ))
      (E := (cell12537 ⟨22, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41656800658367 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142003974381 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_23 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (10409889454749 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (71002113681 / 3125000000000 : ℝ))
      (E := (cell12537 ⟨23, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (10409889454749 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (71002113681 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_24 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (4162232710213 / 5000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (56801790293 / 2500000000000 : ℝ))
      (E := (cell12537 ⟨24, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (4162232710213 / 5000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (56801790293 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_25 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83210216982853 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272075632119 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨25, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83210216982853 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272075632119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_26 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (66540643153 / 80000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272079585571 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨26, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (66540643153 / 80000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272079585571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_27 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83141415047099 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272083591941 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨27, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83141415047099 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272083591941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_28 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16621410053643 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142005474731 / 6250000000000 : ℝ))
      (E := (cell12537 ⟨28, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16621410053643 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142005474731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_29 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (3322908382903 / 4000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136045799727 / 50000000000000 : ℝ))
      (E := (cell12537 ⟨29, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (3322908382903 / 4000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136045799727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_30 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83038392928321 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272095605601 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨30, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83038392928321 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272095605601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_31 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83004100303759 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272099616291 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨31, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83004100303759 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272099616291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_32 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16593966333471 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (284012954181 / 12500000000000 : ℝ))
      (E := (cell12537 ⟨32, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16593966333471 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (284012954181 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_33 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41467793493869 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (11360538001 / 500000000000 : ℝ))
      (E := (cell12537 ⟨33, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41467793493869 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (11360538001 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_34 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16580273246739 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272111635129 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨34, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16580273246739 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272111635129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_35 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (20716792343543 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272115622317 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨35, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (20716792343543 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272115622317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_36 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82832996378273 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (45442392427 / 2000000000000 : ℝ))
      (E := (cell12537 ⟨36, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82832996378273 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (45442392427 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_37 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82798847215261 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454424726603 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨37, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82798847215261 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454424726603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_38 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (10345590231819 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272127599197 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨38, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (10345590231819 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272127599197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_39 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82730620265719 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142008227349 / 6250000000000 : ℝ))
      (E := (cell12537 ⟨39, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82730620265719 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142008227349 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12538_20 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41691318229819 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271926478259 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨20, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41691318229819 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271926478259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_21 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (3333924100383 / 4000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271930481467 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨21, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (3333924100383 / 4000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271930481467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_22 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83313592869961 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135967231061 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨22, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83313592869961 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135967231061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_23 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83279107507773 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567984606061 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨23, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83279107507773 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567984606061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_24 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41622323195077 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271942429981 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨24, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41622323195077 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271942429981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_25 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41605104742209 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567986606143 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨25, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41605104742209 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567986606143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_26 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83175796758047 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135975234869 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨26, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83175796758047 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135975234869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_27 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83141408178689 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (35499288309 / 1562500000000 : ℝ))
      (E := (cell12538 ⟨27, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83141408178689 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (35499288309 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_28 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83107043714159 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454391686383 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨28, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83107043714159 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454391686383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_29 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83072703332437 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135981235621 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨29, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83072703332437 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135981235621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_30 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (16607677400333 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271966455219 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨30, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (16607677400333 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271966455219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_31 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (20751023672537 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271970444451 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨31, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (20751023672537 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271970444451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_32 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (20742456591589 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271974440859 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨32, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (20742456591589 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271974440859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_33 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (20733895499729 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271978446141 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨33, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (20733895499729 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271978446141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_34 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82901361556617 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271982461763 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨34, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82901361556617 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271982461763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_35 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82867165008407 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271986430353 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨35, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82867165008407 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271986430353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_36 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82832992323389 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271990470131 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨36, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82832992323389 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271990470131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_37 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82798843470827 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454398892927 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨37, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82798843470827 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454398892927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_38 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82764718420139 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135999236523 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨38, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82764718420139 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135999236523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_39 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82730617140897 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136001218499 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨39, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82730617140897 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136001218499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12539_20 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16676525476023 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135898672271 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨20, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16676525476023 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135898672271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_21 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20837023436863 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271801319091 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨21, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20837023436863 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271801319091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_22 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20828396106199 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (35496958283 / 1562500000000 : ℝ))
      (E := (cell12539 ⟨22, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20828396106199 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (35496958283 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_23 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41639549689561 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271809323367 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨23, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41639549689561 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271809323367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_24 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83244638577577 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271813360999 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨24, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83244638577577 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271813360999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_25 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41605100993737 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271817329869 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨25, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41605100993737 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271817329869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_26 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (10396973697037 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271821350029 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨26, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (10396973697037 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271821350029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_27 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20785350327923 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271825307777 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨27, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20785350327923 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271825307777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_28 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83107037161479 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271829322787 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨28, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83107037161479 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271829322787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_29 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20768174273409 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283979167409 / 12500000000000 : ℝ))
      (E := (cell12539 ⟨29, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20768174273409 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283979167409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_30 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41519190538153 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (3549745783 / 156250000000 : ℝ))
      (E := (cell12539 ⟨30, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41519190538153 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (3549745783 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_31 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41502044538899 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567960331863 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨31, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41502044538899 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567960331863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_32 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41484910533289 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283980662897 / 12500000000000 : ℝ))
      (E := (cell12539 ⟨32, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41484910533289 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283980662897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_33 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82935577011277 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271849347049 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨33, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82935577011277 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271849347049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_34 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16580271376137 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271853343427 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨34, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16580271376137 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271853343427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_35 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20716790160937 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (70995542253 / 3125000000000 : ℝ))
      (E := (cell12539 ⟨35, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20716790160937 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (70995542253 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_36 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82832988269573 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271861315431 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨36, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82832988269573 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271861315431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_37 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82798839727423 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (90874614059 / 4000000000000 : ℝ))
      (E := (cell12539 ⟨37, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82798839727423 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (90874614059 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_38 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82764714986717 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567967335873 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨38, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82764714986717 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567967335873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_39 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (8273061401703 / 10000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271873350463 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨39, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (8273061401703 / 10000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271873350463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12540_20 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41691309151139 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567917066243 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨20, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41691309151139 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567917066243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_21 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (2604627655843 / 3125000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227167226921 / 10000000000000 : ℝ))
      (E := (cell12540 ⟨21, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (2604627655843 / 3125000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227167226921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_22 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83313575981239 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283959531547 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨22, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83313575981239 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283959531547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_23 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83279091252041 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271680276827 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨23, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83279091252041 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271680276827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_24 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (8324463076653 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135842144031 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨24, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (8324463076653 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135842144031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_25 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (4160509724601 / 5000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567922057813 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨25, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (4160509724601 / 5000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567922057813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_26 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83175782395997 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271692284849 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨26, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83175782395997 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271692284849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_27 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83141394446109 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135848138397 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨27, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83141394446109 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135848138397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_28 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83107030610173 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271700268313 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨28, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83107030610173 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271700268313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_29 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83072690856171 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271704262019 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨29, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83072690856171 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271704262019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_30 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41519187576123 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271708260297 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨30, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41519187576123 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271708260297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_31 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41502041733353 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271712265297 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨31, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41502041733353 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271712265297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_32 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82969815768021 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135858139471 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨32, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82969815768021 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135858139471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_33 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82935572024821 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135860122179 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨33, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82935572024821 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135860122179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_34 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (10362669025737 / 12500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567931070031 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨34, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (10362669025737 / 12500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567931070031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_35 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16573431256039 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271728270319 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨35, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16573431256039 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271728270319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_36 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (3313319368673 / 4000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135866137263 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨36, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (3313319368673 / 4000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135866137263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_37 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82798835985049 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271736234871 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨37, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82798835985049 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271736234871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_38 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (5172794472143 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271740269219 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨38, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (5172794472143 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271740269219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_39 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16546122178823 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454348852113 / 20000000000000 : ℝ))
      (E := (cell12540 ⟨39, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16546122178823 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454348852113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12541_20 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41691304613063 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (17746400309 / 781250000000 : ℝ))
      (E := (cell12541 ⟨20, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41691304613063 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (17746400309 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_21 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83348076228147 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283942901907 / 12500000000000 : ℝ))
      (E := (cell12541 ⟨21, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83348076228147 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283942901907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_22 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (10414195942411 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271547228917 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨22, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (10414195942411 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271547228917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_23 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83279083126527 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135775613147 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨23, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83279083126527 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135775613147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_24 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (20811155739253 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567888802793 / 25000000000000 : ℝ))
      (E := (cell12541 ⟨24, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (20811155739253 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567888802793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_25 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41605093499029 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271559245479 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨25, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41605093499029 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271559245479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_26 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (1663515504343 / 2000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135781607897 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨26, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (1663515504343 / 2000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135781607897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_27 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83141387581939 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271567241977 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨27, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83141387581939 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271567241977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_28 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41553512030121 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567892802511 / 25000000000000 : ℝ))
      (E := (cell12541 ⟨28, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41553512030121 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567892802511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_29 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83072684620041 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135787619743 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨29, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83072684620041 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135787619743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_30 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41519184614741 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271579215759 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨30, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41519184614741 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271579215759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_31 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83004077856873 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135791628993 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨31, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83004077856873 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135791628993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_32 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (20742452617671 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (17746775399 / 781250000000 : ℝ))
      (E := (cell12541 ⟨32, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (20742452617671 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (17746775399 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_33 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41467783519773 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135795627603 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨33, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41467783519773 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135795627603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_34 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82901347532251 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135797606631 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨34, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82901347532251 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135797606631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_35 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (20716787979437 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271599243637 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨35, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (20716787979437 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271599243637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_36 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (10354122520643 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271603230141 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨36, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (10354122520643 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271603230141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_37 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (10349854030463 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271607232151 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨37, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (10349854030463 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271607232151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_38 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82764708122849 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227161125023 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨38, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82764708122849 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227161125023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_39 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (16546121554431 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271615226011 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨39, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (16546121554431 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271615226011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12542_20 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83382600151659 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271410268281 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨20, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83382600151659 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271410268281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_21 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83348067470963 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271414273801 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨21, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83348067470963 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271414273801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_22 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (1301774360921 / 1562500000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135709129867 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨22, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (1301774360921 / 1562500000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135709129867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_23 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83279075002581 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (22714222301 / 1000000000000 : ℝ))
      (E := (cell12542 ⟨23, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83279075002581 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (22714222301 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_24 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83244615149023 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (3549103511 / 156250000000 : ℝ))
      (E := (cell12542 ⟨24, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83244615149023 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (3549103511 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_25 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (16642035901117 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135715127897 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨25, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (16642035901117 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135715127897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_26 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41587884019877 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283929282459 / 12500000000000 : ℝ))
      (E := (cell12542 ⟨26, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41587884019877 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283929282459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_27 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83141380719181 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271438261753 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨27, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83141380719181 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271438261753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_28 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (16621403502337 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271442264881 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨28, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (16621403502337 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271442264881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_29 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (2596021199539 / 3125000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227144627167 / 10000000000000 : ℝ))
      (E := (cell12542 ⟨29, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (2596021199539 / 3125000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227144627167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_30 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (5189897706751 / 6250000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135725113001 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨30, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (5189897706751 / 6250000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135725113001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_31 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83004072248299 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271454246999 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨31, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83004072248299 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271454246999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_32 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82969805174567 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271458278109 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨32, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82969805174567 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271458278109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_33 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41467781027727 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454292452491 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨33, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41467781027727 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454292452491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_34 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (331605371439 / 400000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271466260023 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨34, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (331605371439 / 400000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271466260023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_35 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41433573778203 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271470272051 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨35, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41433573778203 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271470272051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_36 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (8283297611453 / 10000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135737120457 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨36, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (8283297611453 / 10000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135737120457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_37 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (20699707125847 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271478225989 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨37, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (20699707125847 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271478225989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_38 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82764704692401 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271482227839 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨38, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82764704692401 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271482227839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_39 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41365302325573 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454297249361 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨39, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41365302325573 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454297249361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12543_20 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (667060728631 / 800000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271281292899 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨20, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (667060728631 / 800000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271281292899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_21 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (2604626834857 / 3125000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (90851413131 / 4000000000000 : ℝ))
      (E := (cell12543 ⟨21, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (2604626834857 / 3125000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (90851413131 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_22 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41656775330103 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227128934483 / 10000000000000 : ℝ))
      (E := (cell12543 ⟨22, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41656775330103 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227128934483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_23 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83279066880203 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271293346581 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨23, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83279066880203 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271293346581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_24 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41622303671281 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454259467463 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨24, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41622303671281 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454259467463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_25 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41605086007301 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271301320577 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨25, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41605086007301 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271301320577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_26 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83175760863809 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135652649839 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨26, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83175760863809 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135652649839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_27 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (20785343464459 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271309336123 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨27, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (20785343464459 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271309336123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_28 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83107010964501 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271313315927 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨28, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83107010964501 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271313315927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_29 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83072672151789 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135658650051 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨29, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83072672151789 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135658650051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_30 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41519178693923 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271321291029 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨30, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41519178693923 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271321291029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_31 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41502033320491 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (113566264543 / 5000000000000 : ℝ))
      (E := (cell12543 ⟨31, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41502033320491 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (113566264543 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_32 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (8296979987967 / 10000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283916162689 / 12500000000000 : ℝ))
      (E := (cell12543 ⟨32, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (8296979987967 / 10000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283916162689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_33 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82935557072543 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271333324677 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨33, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82935557072543 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271333324677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_34 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (10362667273549 / 12500000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271337303229 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨34, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (10362667273549 / 12500000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271337303229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_35 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82867143196169 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567835324237 / 25000000000000 : ℝ))
      (E := (cell12543 ⟨35, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82867143196169 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567835324237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_36 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82832972064983 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271345306847 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨36, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82832972064983 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271345306847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_37 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82798824764101 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271349333711 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨37, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82798824764101 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271349333711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_38 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (16552940252589 / 20000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135676659709 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨38, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (16552940252589 / 20000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135676659709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_39 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82730601531091 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454271464589 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨39, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82730601531091 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454271464589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12544_20 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (2605705687743 / 3125000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567788107483 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨20, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (2605705687743 / 3125000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567788107483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_21 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83348049961529 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135578218483 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨21, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83348049961529 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135578218483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_22 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41656771111537 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454232085179 / 20000000000000 : ℝ))
      (E := (cell12544 ⟨22, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41656771111537 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454232085179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_23 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83279058759391 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271164400739 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨23, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83279058759391 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271164400739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_24 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (8324459953763 / 10000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135584211819 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨24, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (8324459953763 / 10000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135584211819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_25 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20802541131277 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271172439829 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨25, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20802541131277 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271172439829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_26 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16635150737863 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (113558822631 / 5000000000000 : ℝ))
      (E := (cell12544 ⟨26, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16635150737863 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (113558822631 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_27 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83141366997903 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135590203331 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨27, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83141366997903 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135590203331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_28 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83107004418691 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227118442163 / 10000000000000 : ℝ))
      (E := (cell12544 ⟨28, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83107004418691 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227118442163 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_29 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16614533183933 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271188441729 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨29, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16614533183933 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271188441729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_30 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20759587867243 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271192410841 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨30, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20759587867243 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271192410841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_31 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20751015258731 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271196448087 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨31, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20751015258731 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271196448087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_32 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82969794585993 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (70975013699 / 3125000000000 : ℝ))
      (E := (cell12544 ⟨32, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82969794585993 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (70975013699 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_33 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20733888022703 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271204441873 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨33, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20733888022703 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271204441873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_34 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (2590666672443 / 3125000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271208401471 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨34, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (2590666672443 / 3125000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271208401471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_35 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20716784709259 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271212435559 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨35, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20716784709259 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271212435559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_36 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41416484008251 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135608213971 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨36, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41416484008251 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135608213971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_37 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41399410512921 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567805109499 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨37, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41399410512921 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567805109499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_38 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41382348917239 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135612203799 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨38, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41382348917239 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135612203799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_39 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20682649602997 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135614227217 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨39, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20682649602997 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135614227217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12545_20 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (2084564323459 / 2500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454204712571 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨20, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (2084564323459 / 2500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454204712571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_21 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83348041209279 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (4435600781 / 195312500000 : ℝ))
      (E := (cell12545 ⟨21, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83348041209279 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (4435600781 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_22 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20828383446887 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271031561239 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨22, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20828383446887 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271031561239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_23 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41639525320073 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271035567573 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨23, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41639525320073 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271035567573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_24 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (3329783669369 / 4000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (141939972773 / 6250000000000 : ℝ))
      (E := (cell12545 ⟨24, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (3329783669369 / 4000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (141939972773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_25 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (5200634814819 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271043555169 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨25, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (5200634814819 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271043555169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_26 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83175746516271 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271047601691 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨26, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83175746516271 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271047601691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_27 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83141360139381 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (141940724389 / 6250000000000 : ℝ))
      (E := (cell12545 ⟨27, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83141360139381 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (141940724389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_28 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41553498937127 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283881947749 / 12500000000000 : ℝ))
      (E := (cell12545 ⟨28, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41553498937127 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283881947749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_29 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20768164922219 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271059579603 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨29, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20768164922219 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271059579603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_30 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (16607669110279 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135531792719 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨30, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (16607669110279 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135531792719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_31 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83004055430123 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271067601643 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨31, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83004055430123 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271067601643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_32 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (16593957858707 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271071571591 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨32, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (16593957858707 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271071571591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_33 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82935547110263 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271075555473 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨33, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82935547110263 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271075555473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_34 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82901328849103 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567769888687 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨34, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82901328849103 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567769888687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_35 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (2589597952469 / 3125000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271083570653 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨35, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (2589597952469 / 3125000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271083570653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_36 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (1294265062017 / 1562500000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135543802099 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨36, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (1294265062017 / 1562500000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135543802099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_37 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82798817288611 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454218319501 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨37, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82798817288611 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454218319501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_38 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82764694407001 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271095609751 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨38, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82764694407001 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271095609751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_39 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82730595293837 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271099582563 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨39, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82730595293837 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271099582563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12546_20 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41691281935313 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135447404099 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨20, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41691281935313 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135447404099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_21 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83348032458673 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283862344839 / 12500000000000 : ℝ))
      (E := (cell12546 ⟨21, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83348032458673 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283862344839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_22 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41656762676813 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135451404589 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨22, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41656762676813 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135451404589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_23 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83279042522467 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135453394377 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨23, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83279042522467 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135453394377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_24 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83244583932347 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567727689877 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨24, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83244583932347 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567727689877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_25 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83210149550587 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454182956673 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨25, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83210149550587 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454182956673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_26 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83175739344677 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135459402649 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨26, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83175739344677 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135459402649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_27 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (8314135328227 / 10000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270922769959 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨27, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (8314135328227 / 10000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270922769959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_28 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83106991331189 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270926797017 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨28, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83106991331189 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270926797017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_29 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (4153632672971 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567732693051 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨29, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (4153632672971 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567732693051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_30 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83038339635113 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (90837390253 / 4000000000000 : ℝ))
      (E := (cell12546 ⟨30, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83038339635113 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (90837390253 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_31 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83004049826579 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283867343941 / 12500000000000 : ℝ))
      (E := (cell12546 ⟨31, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83004049826579 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283867343941 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_32 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (16593956800459 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (141933922483 / 6250000000000 : ℝ))
      (E := (cell12546 ⟨32, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (16593956800459 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (141933922483 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_33 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41467771065447 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135473391309 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨33, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41467771065447 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135473391309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_34 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82901324181173 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454190152613 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨34, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82901324181173 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454190152613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_35 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (20716782530521 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270954760849 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨35, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (20716782530521 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270954760849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_36 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82832959922739 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (113547938849 / 5000000000000 : ℝ))
      (E := (cell12546 ⟨36, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82832959922739 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (113547938849 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_37 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (10349851694051 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270962753579 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨37, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (10349851694051 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270962753579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_38 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (16552938196103 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135483404253 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨38, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (16552938196103 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135483404253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_39 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41365296088319 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567742691511 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨39, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41365296088319 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567742691511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12547_20 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (2605704837643 / 3125000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283845756179 / 12500000000000 : ℝ))
      (E := (cell12547 ⟨20, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (2605704837643 / 3125000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283845756179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_21 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83348023709711 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283846253757 / 12500000000000 : ℝ))
      (E := (cell12547 ⟨21, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83348023709711 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283846253757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_22 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83313516921309 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (70961689159 / 3125000000000 : ℝ))
      (E := (cell12547 ⟨22, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83313516921309 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (70961689159 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_23 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41639517203177 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135389002973 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨23, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41639517203177 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135389002973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_24 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20811144032999 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (70961937783 / 3125000000000 : ℝ))
      (E := (cell12547 ⟨24, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20811144032999 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (70961937783 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_25 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83210142065559 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270786007651 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨25, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83210142065559 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270786007651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_26 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20793933043633 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270790005037 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨26, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20793933043633 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270790005037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_27 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (8314134642657 / 10000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270794004291 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨27, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (8314134642657 / 10000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270794004291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_28 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83106984789497 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567699502063 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨28, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83106984789497 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567699502063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_29 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41536323615649 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270802019529 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨29, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41536323615649 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270802019529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_30 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41519166860063 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270806040497 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨30, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41519166860063 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270806040497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_31 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20751011056073 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (35481406481 / 1562500000000 : ℝ))
      (E := (cell12547 ⟨31, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20751011056073 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (35481406481 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_32 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41484889356137 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135407001389 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨32, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41484889356137 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135407001389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_33 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41467768576353 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (227081800617 / 10000000000000 : ℝ))
      (E := (cell12547 ⟨33, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41467768576353 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (227081800617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_34 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (5181332469649 / 6250000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113541101321 / 5000000000000 : ℝ))
      (E := (cell12547 ⟨34, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (5181332469649 / 6250000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113541101321 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_35 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82867125766263 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270826006147 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨35, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82867125766263 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270826006147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_36 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82832955877457 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (90833200197 / 4000000000000 : ℝ))
      (E := (cell12547 ⟨36, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82832955877457 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (90833200197 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_37 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82798809817233 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113541701177 / 5000000000000 : ℝ))
      (E := (cell12547 ⟨37, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82798809817233 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113541701177 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_38 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82764687555017 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135419001933 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨38, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82764687555017 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135419001933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_39 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82730589060391 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (18166736039 / 800000000000 : ℝ))
      (E := (cell12547 ⟨39, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82730589060391 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (18166736039 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12548_20 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83382545740207 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90825493793 / 4000000000000 : ℝ))
      (E := (cell12548 ⟨20, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83382545740207 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90825493793 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_21 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (10418501870299 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283830162167 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨21, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (10418501870299 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283830162167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_22 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83313508490597 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567661323243 / 25000000000000 : ℝ))
      (E := (cell12548 ⟨22, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83313508490597 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567661323243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_23 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41639513145903 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113532466791 / 5000000000000 : ℝ))
      (E := (cell12548 ⟨23, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41639513145903 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113532466791 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_24 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (20811142083293 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283831664127 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨24, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (20811142083293 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283831664127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_25 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83210134582019 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270657286411 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨25, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83210134582019 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270657286411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_26 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (20793931251459 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135330658859 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨26, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (20793931251459 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135330658859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_27 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (2078533489307 / 2500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90826611729 / 4000000000000 : ℝ))
      (E := (cell12548 ⟨27, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (2078533489307 / 2500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90826611729 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_28 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (10388372281147 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135334666301 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨28, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (10388372281147 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135334666301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_29 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (8307264100451 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113533666079 / 5000000000000 : ℝ))
      (E := (cell12548 ⟨29, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (8307264100451 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113533666079 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_30 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83038327806433 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135338660481 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨30, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83038327806433 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135338660481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_31 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41502019311631 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567670333223 / 25000000000000 : ℝ))
      (E := (cell12548 ⟨31, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41502019311631 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567670333223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_32 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82969773423471 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283835662593 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨32, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82969773423471 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283835662593 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_33 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82935532175697 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270689343269 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨33, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82935532175697 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270689343269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_34 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82901314848737 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (141918330389 / 6250000000000 : ℝ))
      (E := (cell12548 ⟨34, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82901314848737 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (141918330389 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_35 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41433560705773 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270697306547 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨35, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41433560705773 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270697306547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_36 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82832951833239 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270701288037 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨36, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82832951833239 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270701288037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_37 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (20699701520771 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270705290069 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨37, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (20699701520771 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270705290069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_38 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82764684130509 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135354656601 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨38, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82764684130509 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135354656601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_39 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41365292972547 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270713299061 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨39, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41365292972547 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270713299061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12549_20 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (1042281708469 / 1250000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135254318057 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨20, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (1042281708469 / 1250000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135254318057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_21 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (16669601243343 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (18164101417 / 800000000000 : ℝ))
      (E := (cell12549 ⟨21, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (16669601243343 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (18164101417 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_22 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (5207093753843 / 6250000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270516645453 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨22, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (5207093753843 / 6250000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270516645453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_23 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41639509089411 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270520661711 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨23, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41639509089411 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270520661711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_24 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41622280267937 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270524671389 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨24, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41622280267937 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270524671389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_25 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41605063549983 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270528619647 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨25, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41605063549983 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270528619647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_26 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83175717838589 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270532626533 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨26, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83175717838589 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270532626533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_27 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83141332719401 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (56763415919 / 2500000000000 : ℝ))
      (E := (cell12549 ⟨27, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83141332719401 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (56763415919 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_28 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83106971710227 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135270326583 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨28, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83106971710227 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135270326583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_29 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41536317389527 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454108923977 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨29, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41536317389527 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454108923977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_30 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20759580473509 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270548656217 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨30, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20759580473509 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270548656217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_31 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83004033023487 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135276323667 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨31, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83004033023487 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135276323667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_32 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (16593953627177 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135278326813 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨32, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (16593953627177 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135278326813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_33 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82935527199867 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (113528033839 / 5000000000000 : ℝ))
      (E := (cell12549 ⟨33, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82935527199867 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (113528033839 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_34 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82901310184231 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270564659663 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨34, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82901310184231 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270564659663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_35 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82867117057933 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567642165513 / 25000000000000 : ℝ))
      (E := (cell12549 ⟨35, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82867117057933 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567642165513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_36 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41416473895043 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567643156579 / 25000000000000 : ℝ))
      (E := (cell12549 ⟨36, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41416473895043 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567643156579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_37 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82798802349963 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270576670489 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨37, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82798802349963 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270576670489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_38 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (8276468070699 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270580677829 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨38, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (8276468070699 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270580677829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_39 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82730582830749 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270584648601 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨39, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82730582830749 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270584648601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

end BstLean.Part268
