import BstLean.Part268CellShard7Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12525_0 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (8407867507963 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273529180151 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨0, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (8407867507963 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273529180151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_1 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (16808728693167 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284191647039 / 12500000000000 : ℝ))
      (E := (cell12525 ⟨1, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (16808728693167 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284191647039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_2 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (16801727373291 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136768590017 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨2, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (16801727373291 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136768590017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_3 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83973655244809 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (454708240109 / 20000000000000 : ℝ))
      (E := (cell12525 ⟨3, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83973655244809 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (454708240109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_4 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41969349282207 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136772594459 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨4, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41969349282207 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136772594459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_5 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41951883394487 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (22735492117 / 1000000000000 : ℝ))
      (E := (cell12525 ⟨5, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41951883394487 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (22735492117 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_6 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (8386885988239 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (8881067037 / 390625000000 : ℝ))
      (E := (cell12525 ⟨6, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (8386885988239 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (8881067037 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_7 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83833977808747 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273557162197 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨7, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83833977808747 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273557162197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_8 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20949780133081 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284195145479 / 12500000000000 : ℝ))
      (E := (cell12525 ⟨8, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20949780133081 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284195145479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_9 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83764288017583 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227356517399 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨9, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83764288017583 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227356517399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_10 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41864740114587 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227356920003 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨10, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41864740114587 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227356920003 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_11 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20923674282983 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227357319101 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨11, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20923674282983 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227357319101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_12 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20914984672719 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136788576859 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨12, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20914984672719 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136788576859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_13 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41812602435603 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273581152789 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨13, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41812602435603 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273581152789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_14 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41795247819153 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136792597291 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨14, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41795247819153 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136792597291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_15 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (10444476369717 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136794584463 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨15, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (10444476369717 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136794584463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_16 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83521150795239 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136796569857 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨16, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83521150795239 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136796569857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_17 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41743257558367 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273597170689 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨17, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41743257558367 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273597170689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_18 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (83451903888317 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136800575401 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨18, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (83451903888317 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136800575401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_19 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (4170865853813 / 5000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273605143287 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨19, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (4170865853813 / 5000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273605143287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12526_0 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (84078659525313 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (3637439211 / 160000000000 : ℝ))
      (E := (cell12526 ⟨0, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (84078659525313 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (3637439211 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_1 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16808725647701 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284175439569 / 12500000000000 : ℝ))
      (E := (cell12526 ⟨1, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16808725647701 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284175439569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_2 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (84008621965647 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273407476739 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨2, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (84008621965647 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273407476739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_3 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41986820335031 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273411454449 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨3, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41986820335031 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273411454449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_4 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16787736863053 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136707729323 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨4, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16787736863053 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136707729323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_5 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16780750572993 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142088718627 / 6250000000000 : ℝ))
      (E := (cell12526 ⟨5, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16780750572993 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142088718627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_6 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (4193442314153 / 5000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273423465189 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨6, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (4193442314153 / 5000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273423465189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_7 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (2095849113341 / 2500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273427484079 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨7, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (2095849113341 / 2500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273427484079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_8 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83799107580981 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273431446679 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨8, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83799107580981 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273431446679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_9 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (20941068847387 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454687095307 / 20000000000000 : ℝ))
      (E := (cell12526 ⟨9, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (20941068847387 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454687095307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_10 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83729467923993 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (35522491641 / 1562500000000 : ℝ))
      (E := (cell12526 ⟨10, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83729467923993 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (35522491641 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_11 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (1673893702983 / 2000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142090217327 / 6250000000000 : ℝ))
      (E := (cell12526 ⟨11, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (1673893702983 / 2000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (142090217327 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_12 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (2091498175751 / 2500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273447461943 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨12, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (2091498175751 / 2500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273447461943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_13 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (10453149191483 / 12500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136725712847 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨13, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (10453149191483 / 12500000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136725712847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_14 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16718096924001 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (35522741139 / 1562500000000 : ℝ))
      (E := (cell12526 ⟨14, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16718096924001 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (35522741139 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_15 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83555800260027 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568364857879 / 25000000000000 : ℝ))
      (E := (cell12526 ⟨15, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83555800260027 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568364857879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_16 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83521140417673 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273463427351 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨16, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83521140417673 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273463427351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_17 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83486505058861 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454693485191 / 20000000000000 : ℝ))
      (E := (cell12526 ⟨17, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83486505058861 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454693485191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_18 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83451894149691 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284183929079 / 12500000000000 : ℝ))
      (E := (cell12526 ⟨18, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83451894149691 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284183929079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_19 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (83417307656433 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568368863113 / 25000000000000 : ℝ))
      (E := (cell12526 ⟨19, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (83417307656433 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568368863113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12527_0 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (21019660993371 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273269828651 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨0, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (21019660993371 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273269828651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_1 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (84043613013621 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273273794071 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨1, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (84043613013621 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273273794071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_2 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16801721413449 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136638913209 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨2, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16801721413449 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136638913209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_3 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (1049670326221 / 1250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284160227407 / 12500000000000 : ℝ))
      (E := (cell12527 ⟨3, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (1049670326221 / 1250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284160227407 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_4 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83938670068443 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568321445369 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨4, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83938670068443 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568321445369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_5 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83903738943241 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273289779623 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨5, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83903738943241 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273289779623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_6 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (83868832685977 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136646911069 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨6, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (83868832685977 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136646911069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_7 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41916975630369 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136648900651 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨7, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41916975630369 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136648900651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_8 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (20949773657951 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273301782887 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨8, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (20949773657951 / 25000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273301782887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_9 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (2094106569091 / 2500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273305774503 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨9, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (2094106569091 / 2500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273305774503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_10 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41864727810449 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568327445877 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨10, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41864727810449 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568327445877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_11 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16738934633683 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273313817009 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨11, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16738934633683 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273313817009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_12 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (8365991537121 / 10000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454663553143 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨12, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (8365991537121 / 10000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454663553143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_13 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (10453147774311 / 12500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273321810381 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨13, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (10453147774311 / 12500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273321810381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_14 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (5224404600227 / 6250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273325783077 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨14, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (5224404600227 / 6250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273325783077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_15 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41777894782103 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136664903031 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨15, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41777894782103 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136664903031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_16 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16704226008391 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454666753773 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨16, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16704226008391 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454666753773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_17 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41743247501399 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (45466755867 / 2000000000000 : ℝ))
      (E := (cell12527 ⟨17, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41743247501399 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (45466755867 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_18 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41725942206417 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136670884233 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨18, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41725942206417 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136670884233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_19 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (651697642487 / 781250000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454669151489 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨19, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (651697642487 / 781250000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454669151489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12528_0 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (4203931421207 / 5000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (90925608131 / 4000000000000 : ℝ))
      (E := (cell12528 ⟨0, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (4203931421207 / 5000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (90925608131 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_1 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (42021798895591 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (28414302279 / 1250000000000 : ℝ))
      (E := (cell12528 ⟨1, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (42021798895591 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (28414302279 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_2 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5250537010703 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568287042809 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨2, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5250537010703 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568287042809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_3 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5248350720479 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136576089621 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨3, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5248350720479 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136576089621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_4 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (16787731164789 / 20000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454631231483 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨4, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (16787731164789 / 20000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454631231483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_5 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83903725023803 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136580086147 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨5, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83903725023803 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136580086147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_6 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41934409545569 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (284145521799 / 12500000000000 : ℝ))
      (E := (cell12528 ⟨6, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41934409545569 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (284145521799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_7 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83833937990041 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136584085913 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨7, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83833937990041 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136584085913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_8 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (10474885210599 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (113658608623 / 5000000000000 : ℝ))
      (E := (cell12528 ⟨8, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (10474885210599 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (113658608623 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_9 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5235265633741 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (71036755747 / 3125000000000 : ℝ))
      (E := (cell12528 ⟨9, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5235265633741 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (71036755747 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_10 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (5233090207493 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273180155487 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨10, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (5233090207493 / 6250000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273180155487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_11 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (3347786447589 / 4000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273184152293 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨11, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (3347786447589 / 4000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273184152293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_12 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83659903714387 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273188181181 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨12, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83659903714387 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273188181181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_13 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83625170859079 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273192132559 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨13, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83625170859079 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273192132559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_14 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41795231294593 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (17759345211 / 781250000000 : ℝ))
      (E := (cell12528 ⟨14, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41795231294593 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (17759345211 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_15 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83555778870273 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568300044069 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨15, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83555778870273 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568300044069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_16 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20880279917021 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273204164257 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨16, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20880279917021 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273204164257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_17 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (83486484948543 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273208156497 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨17, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (83486484948543 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273208156497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_18 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41725937338873 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136606079153 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨18, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41725937338873 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136606079153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_19 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (8341728882197 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454643234949 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨19, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (8341728882197 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454643234949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12529_0 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (42039306438641 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273010630747 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨0, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (42039306438641 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273010630747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_1 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (21010895642797 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136507311741 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨1, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (21010895642797 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136507311741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_2 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (84008577277657 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227301862687 / 10000000000000 : ℝ))
      (E := (cell12529 ⟨2, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (84008577277657 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227301862687 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_3 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20993399240003 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (142063912017 / 6250000000000 : ℝ))
      (E := (cell12529 ⟨3, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20993399240003 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (142063912017 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_4 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20984660395443 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273026586461 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨4, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20984660395443 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273026586461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_5 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (10487963888331 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273030618139 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨5, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (10487963888331 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273030618139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_6 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83868805498543 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136517289941 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨6, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83868805498543 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136517289941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_7 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20958481180387 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273038595651 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨7, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20958481180387 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273038595651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_8 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (10474883592493 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273042615399 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨8, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (10474883592493 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273042615399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_9 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41882118759099 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227304658873 / 10000000000000 : ℝ))
      (E := (cell12529 ⟨9, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41882118759099 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227304658873 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_10 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83729431020963 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136525290479 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨10, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83729431020963 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136525290479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_11 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (2092366230327 / 2500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136527299593 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨11, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (2092366230327 / 2500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136527299593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_12 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83659892059569 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454611718439 / 20000000000000 : ℝ))
      (E := (cell12529 ⟨12, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83659892059569 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454611718439 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_13 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (16725031905127 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273062566521 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨13, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (16725031905127 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273062566521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_14 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41795225788333 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273066586569 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨14, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41795225788333 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273066586569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_15 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41777884089113 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136535300153 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨15, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41777884089113 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136535300153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_16 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41760554648031 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136537277679 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨16, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41760554648031 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136537277679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_17 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (16697294979219 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136539286793 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨17, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (16697294979219 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136539286793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_18 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (83451864944427 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273082602151 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨18, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (83451864944427 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273082602151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_19 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20854319851833 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136543293939 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨19, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20854319851833 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136543293939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12530_0 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (21019649333227 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272881111071 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨0, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (21019649333227 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272881111071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_1 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (84043567353639 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136442529871 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨1, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (84043567353639 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136442529871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_2 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (84008562386469 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272889077647 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨2, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (84008562386469 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272889077647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_3 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20993395598681 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136446529173 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨3, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20993395598681 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136446529173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_4 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41969313670961 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272897068617 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨4, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41969313670961 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272897068617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_5 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41951848595889 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136450529623 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨5, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41951848595889 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136450529623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_6 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (2620899747131 / 3125000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (71028284267 / 3125000000000 : ℝ))
      (E := (cell12530 ⟨6, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (2620899747131 / 3125000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (71028284267 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_7 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83833911455259 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272909072779 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨7, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83833911455259 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272909072779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_8 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (4189952789863 / 5000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (90916522149 / 4000000000000 : ℝ))
      (E := (cell12530 ⟨8, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (4189952789863 / 5000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (90916522149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_9 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83764224898663 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272917046989 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨9, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83764224898663 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272917046989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_10 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83729418724123 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136460529963 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨10, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83729418724123 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136460529963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_11 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83694637238479 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272925041589 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨11, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83694637238479 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272925041589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_12 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (16731976081351 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568232264209 / 25000000000000 : ℝ))
      (E := (cell12530 ⟨12, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (16731976081351 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568232264209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_13 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (83625148194157 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272933054171 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨13, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (83625148194157 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272933054171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_14 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10448805070759 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136468519941 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨14, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10448805070759 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136468519941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_15 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41777878744033 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272941020007 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨15, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41777878744033 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272941020007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_16 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41760549462943 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272945058507 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨16, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41760549462943 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2272945058507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_17 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (5217904052841 / 6250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136474522309 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨17, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (5217904052841 / 6250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136474522309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_18 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20862963803219 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227295304179 / 10000000000000 : ℝ))
      (E := (cell12530 ⟨18, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20862963803219 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (227295304179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_19 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10427158749303 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136478527541 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨19, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10427158749303 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136478527541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12531_0 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (84078581791019 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568187896613 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨0, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (84078581791019 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568187896613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_1 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (42021776069267 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454551121347 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨1, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (42021776069267 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454551121347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_2 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16801709499537 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272759581403 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨2, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16801709499537 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272759581403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_3 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83973567831799 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136381788733 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨3, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83973567831799 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136381788733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_4 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20984653276099 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136383801941 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨4, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20984653276099 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136383801941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_5 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (8390368327919 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272771611439 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨5, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (8390368327919 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272771611439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_6 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16773755664017 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227277560851 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨6, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16773755664017 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227277560851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_7 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41916949095587 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227277960321 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨7, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41916949095587 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227277960321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_8 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83799042856739 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272783603399 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨8, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83799042856739 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272783603399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_9 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20941053070313 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272787558679 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨9, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20941053070313 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272787558679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_10 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41864703214683 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227279159239 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨10, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41864703214683 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227279159239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_11 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83694625265923 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272795595603 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨11, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83694625265923 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272795595603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_12 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41829934377973 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (22727995751 / 1000000000000 : ℝ))
      (E := (cell12531 ⟨12, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41829934377973 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (22727995751 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_13 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20906284216161 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227280359551 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨13, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20906284216161 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227280359551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_14 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83590429557403 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568201886737 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨14, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83590429557403 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568201886737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_15 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83555746799791 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227281155167 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨15, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83555746799791 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227281155167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_16 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20880272139389 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227281555737 / 10000000000000 : ℝ))
      (E := (cell12531 ⟨16, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20880272139389 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (227281555737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_17 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83486454796623 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568204892399 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨17, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83486454796623 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568204892399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_18 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (83451845483093 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568205883859 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨18, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (83451845483093 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568205883859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_19 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20854315145811 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272827576357 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨19, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20854315145811 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272827576357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12532_0 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (42039283125807 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272622172479 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨0, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (42039283125807 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272622172479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_1 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (84043536925873 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272626148829 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨1, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (84043536925873 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272626148829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_2 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (10501066576413 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136315069071 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨2, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (10501066576413 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136315069071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_3 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83973553271237 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272634149633 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨3, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83973553271237 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272634149633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_4 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83938598869193 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272638134373 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨4, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83938598869193 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272638134373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_5 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (16780733873777 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272642158899 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨5, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (16780733873777 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272642158899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_6 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (4193438236711 / 5000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272646173719 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨6, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (4193438236711 / 5000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272646173719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_7 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83833884929291 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227265012899 / 10000000000000 : ℝ))
      (E := (cell12532 ⟨7, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83833884929291 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227265012899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_8 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41899514959191 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136327074231 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨8, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41899514959191 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136327074231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_9 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83764199665963 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454531624761 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨9, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83764199665963 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454531624761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_10 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20932348534173 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136331060163 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨10, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20932348534173 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136331060163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_11 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (8369461329541 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272666145129 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨11, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (8369461329541 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272666145129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_12 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41829928553571 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227267014699 / 10000000000000 : ℝ))
      (E := (cell12532 ⟨12, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41829928553571 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (227267014699 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_13 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (16725025107419 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136337066221 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨13, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (16725025107419 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136337066221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_14 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83590418550659 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284084763471 / 12500000000000 : ℝ))
      (E := (cell12532 ⟨14, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83590418550659 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284084763471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_15 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41777868056701 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272682137151 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨15, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41777868056701 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272682137151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_16 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83521078191073 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454537222023 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨16, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83521078191073 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454537222023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_17 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (83486444749597 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (56817253713 / 2500000000000 : ℝ))
      (E := (cell12532 ⟨17, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (83486444749597 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (56817253713 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_18 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41725917877539 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272694141307 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨18, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41725917877539 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272694141307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_19 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (2606789099181 / 3125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272698093469 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨19, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (2606789099181 / 3125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272698093469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12533_0 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (84078550714691 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272492753569 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨0, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (84078550714691 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272492753569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_1 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (84043521715653 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568124185961 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨1, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (84043521715653 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568124185961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_2 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (42004258863663 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136250373933 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨2, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (42004258863663 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136250373933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_3 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41986769356519 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272504774849 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨3, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41986769356519 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272504774849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_4 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (10492323079539 / 12500000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284063596983 / 12500000000000 : ℝ))
      (E := (cell12533 ⟨4, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (10492323079539 / 12500000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284063596983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_5 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83903655460863 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (142032047471 / 6250000000000 : ℝ))
      (E := (cell12533 ⟨5, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83903655460863 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (142032047471 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_6 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83868751150597 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568129183559 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨6, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83868751150597 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568129183559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_7 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (8383387166961 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136260383017 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨7, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (8383387166961 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136260383017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_8 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83799016982187 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272524746897 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨8, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83799016982187 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272524746897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_9 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41882093526399 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454505748473 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨9, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41882093526399 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454505748473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_10 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41864690923051 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568133189947 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨10, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41864690923051 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568133189947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_11 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (4184730066347 / 5000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272536748219 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨11, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (4184730066347 / 5000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272536748219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_12 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (4182992273017 / 5000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454508142887 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨12, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (4182992273017 / 5000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454508142887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_13 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (8362511421151 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272544723067 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨13, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (8362511421151 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272544723067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_14 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83590407545839 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136274361173 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨14, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83590407545839 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136274361173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_15 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41777862714449 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568138179577 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨15, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41777862714449 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568138179577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_16 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (16704213565287 / 20000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284069589593 / 12500000000000 : ℝ))
      (E := (cell12533 ⟨16, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (16704213565287 / 20000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284069589593 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_17 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41743217352189 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272560723199 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨17, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41743217352189 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272560723199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_18 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (83451826028829 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (90902589719 / 4000000000000 : ℝ))
      (E := (cell12533 ⟨18, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (83451826028829 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (90902589719 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_19 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20854310441517 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136284361447 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨19, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20854310441517 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136284361447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12534_0 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (84078535180251 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272363445307 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨0, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (84078535180251 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272363445307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_1 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (21010876626969 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454473489919 / 20000000000000 : ℝ))
      (E := (cell12534 ⟨1, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (21010876626969 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454473489919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_2 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (336034011383 / 400000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136185705287 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨2, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (336034011383 / 400000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136185705287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_3 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (209933810393 / 250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568093848813 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨3, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (209933810393 / 250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568093848813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_4 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (10492321300719 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272379412583 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨4, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (10492321300719 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272379412583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_5 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41951820777561 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272383413353 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨5, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41951820777561 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272383413353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_6 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (1310449024519 / 1562500000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227238740593 / 10000000000000 : ℝ))
      (E := (cell12534 ⟨6, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (1310449024519 / 1562500000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227238740593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_7 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83833858412131 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272391398429 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨7, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83833858412131 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272391398429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_8 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83799004048153 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (142024712419 / 6250000000000 : ℝ))
      (E := (cell12534 ⟨8, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83799004048153 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (142024712419 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_9 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41882087220877 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136199707181 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨9, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41882087220877 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136199707181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_10 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83729369557593 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (90896135789 / 4000000000000 : ℝ))
      (E := (cell12534 ⟨10, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83729369557593 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (90896135789 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_11 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83694589360513 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272407404873 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨11, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83694589360513 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272407404873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_12 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41829916907771 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272411393583 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨12, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41829916907771 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272411393583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_13 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (5226568930493 / 6250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (284051920923 / 12500000000000 : ℝ))
      (E := (cell12534 ⟨13, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (5226568930493 / 6250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (284051920923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_14 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83590396542943 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (56810484767 / 2500000000000 : ℝ))
      (E := (cell12534 ⟨14, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83590396542943 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (56810484767 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_15 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41777857373139 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227242341143 / 10000000000000 : ℝ))
      (E := (cell12534 ⟨15, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41777857373139 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (227242341143 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_16 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41760528731821 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136213688629 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨16, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41760528731821 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136213688629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_17 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (20871606165241 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272431410019 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨17, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (20871606165241 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272431410019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_18 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83451816304347 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1109587597 / 48828125000 : ℝ))
      (E := (cell12534 ⟨18, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83451816304347 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1109587597 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_19 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (83417232360071 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454487881279 / 20000000000000 : ℝ))
      (E := (cell12534 ⟨19, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (83417232360071 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (454487881279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12535_0 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (21019629912073 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272234132111 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨0, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (21019629912073 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272234132111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_1 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (84043491302541 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272238150453 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨1, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (84043491302541 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272238150453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_2 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (42004243983287 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272242126271 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨2, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (42004243983287 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272242126271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_3 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (20993377400931 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227224612657 / 10000000000000 : ℝ))
      (E := (cell12535 ⟨3, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (20993377400931 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (227224612657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_4 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41969278088757 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136125051209 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨4, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41969278088757 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136125051209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_5 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41951813825831 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272254120351 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨5, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41951813825831 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272254120351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_6 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (20967180997519 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272258130871 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨6, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (20967180997519 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272258130871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_7 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83833845156853 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136131042067 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨7, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83833845156853 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136131042067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_8 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83798991116281 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136133051943 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨8, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83798991116281 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136133051943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_9 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (654407514319 / 781250000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136135040897 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨9, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (654407514319 / 781250000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136135040897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_10 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41864678635583 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568068520791 / 25000000000000 : ℝ))
      (E := (cell12535 ⟨10, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41864678635583 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568068520791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_11 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (2615455543629 / 3125000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454455623019 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨11, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (2615455543629 / 3125000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454455623019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_12 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41829911086373 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (35504407317 / 1562500000000 : ℝ))
      (E := (cell12535 ⟨12, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41829911086373 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (35504407317 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_13 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83625091566229 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272286065397 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨13, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83625091566229 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272286065397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_14 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83590385541971 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568072528193 / 25000000000000 : ℝ))
      (E := (cell12535 ⟨14, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83590385541971 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568072528193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_15 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41777852032771 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272294100231 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨15, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41777852032771 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272294100231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_16 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41760523551347 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136149045829 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨16, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41760523551347 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136149045829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_17 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (16697282923871 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136151046299 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨17, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (16697282923871 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136151046299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_18 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (8345180658163 / 10000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272306108351 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨18, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (8345180658163 / 10000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272306108351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_19 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (83417222955801 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454462017147 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨19, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (83417222955801 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454462017147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12536_0 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (16815700823763 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272104871771 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨0, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (16815700823763 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272104871771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_1 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (42021738049823 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (142006802901 / 6250000000000 : ℝ))
      (E := (cell12536 ⟨1, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (42021738049823 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (142006802901 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_2 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (420042365449 / 500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136056418557 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨2, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (420042365449 / 500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136056418557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_3 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (1312085860197 / 1562500000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568029213269 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨3, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (1312085860197 / 1562500000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568029213269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_4 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20984635487899 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227212084537 / 10000000000000 : ℝ))
      (E := (cell12536 ⟨4, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20984635487899 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227212084537 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_5 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41951806875241 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272124880529 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨5, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41951806875241 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272124880529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_6 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (10483588801647 / 12500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272128851123 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨6, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (10483588801647 / 12500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272128851123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_7 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (2619807246993 / 3125000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568033205787 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨7, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (2619807246993 / 3125000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568033205787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_8 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (8379897818657 / 10000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272136862441 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨8, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (8379897818657 / 10000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272136862441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_9 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83764149226031 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272140860667 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨9, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83764149226031 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272140860667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_10 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83729344986821 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454428965021 / 20000000000000 : ℝ))
      (E := (cell12536 ⟨10, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83729344986821 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454428965021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_11 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (16738913086757 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (71004650651 / 3125000000000 : ℝ))
      (E := (cell12536 ⟨11, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (16738913086757 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (71004650651 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_12 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83659810531951 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136076427349 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨12, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83659810531951 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136076427349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_13 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83625080246533 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (142009801069 / 6250000000000 : ℝ))
      (E := (cell12536 ⟨13, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83625080246533 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (142009801069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_14 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83590374542921 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272160830503 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨14, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83590374542921 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272160830503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_15 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83555693386689 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454432968571 / 20000000000000 : ℝ))
      (E := (cell12536 ⟨15, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83555693386689 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (454432968571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_16 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83521036743589 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136084429973 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨16, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83521036743589 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136084429973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_17 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (83486404579551 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272172829127 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨17, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (83486404579551 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272172829127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_18 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (2086294921517 / 2500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568044203461 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨18, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (2086294921517 / 2500000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568044203461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_19 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41708606776629 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272180819153 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨19, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41708606776629 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272180819153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12537_0 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (84078488591819 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271975664293 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨0, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (84078488591819 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271975664293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_1 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (10505432612399 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271979653123 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨1, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (10505432612399 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271979653123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_2 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (42004229107713 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (567995914697 / 25000000000000 : ℝ))
      (E := (cell12537 ⟨2, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (42004229107713 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (567995914697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_3 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (20993370125963 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271987632639 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨3, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (20993370125963 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271987632639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_4 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41969263863999 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271991641443 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨4, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41969263863999 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271991641443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_5 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83903599851583 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1135997817991 / 50000000000000 : ℝ))
      (E := (cell12537 ⟨5, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83903599851583 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1135997817991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_6 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83868696838517 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271999624623 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨6, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83868696838517 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2271999624623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_7 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83833818652899 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568000903869 / 25000000000000 : ℝ))
      (E := (cell12537 ⟨7, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83833818652899 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568000903869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_8 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41899482629509 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454401523279 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨8, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41899482629509 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454401523279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_9 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (1675282732427 / 2000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (113600581749 / 5000000000000 : ℝ))
      (E := (cell12537 ⟨9, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (1675282732427 / 2000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (113600581749 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_10 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (20932333176139 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272015620553 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨10, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (20932333176139 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272015620553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_11 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41847276736741 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142001227387 / 6250000000000 : ℝ))
      (E := (cell12537 ⟨11, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41847276736741 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (142001227387 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_12 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83659798893159 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568005909167 / 25000000000000 : ℝ))
      (E := (cell12537 ⟨12, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83659798893159 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568005909167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_13 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41812534464399 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (227202762251 / 10000000000000 : ℝ))
      (E := (cell12537 ⟨13, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41812534464399 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (227202762251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_14 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41795181772897 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568007900499 / 25000000000000 : ℝ))
      (E := (cell12537 ⟨14, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41795181772897 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568007900499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_15 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (2088892067743 / 2500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454407127861 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨15, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (2088892067743 / 2500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454407127861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_16 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83521026386329 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454407924791 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨16, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83521026386329 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454407924791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_17 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (83486394541551 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272043619611 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨17, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (83486394541551 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272043619611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_18 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41725893570747 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272047631571 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨18, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41725893570747 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272047631571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_19 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (2085430103811 / 2500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272051606653 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨19, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (2085430103811 / 2500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272051606653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12538_0 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (42039236533651 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271846509677 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨0, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (42039236533651 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271846509677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_1 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (42021722850589 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135925256377 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨1, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (42021722850589 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135925256377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_2 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (84008443343451 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567963618903 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨2, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (84008443343451 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567963618903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_3 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (16794693191491 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283982308157 / 12500000000000 : ℝ))
      (E := (cell12538 ⟨3, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (16794693191491 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283982308157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_4 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83938513506719 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135931245317 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨4, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83938513506719 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135931245317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_5 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83903585954963 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271866502529 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨5, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83903585954963 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271866502529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_6 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (5241792704131 / 6250000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135935254653 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨6, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (5241792704131 / 6250000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135935254653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_7 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83833805404221 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567968615279 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨7, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83833805404221 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567968615279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_8 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83798952333627 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283984810213 / 12500000000000 : ℝ))
      (E := (cell12538 ⟨8, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83798952333627 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283984810213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_9 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83764124018789 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271882462733 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨9, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83764124018789 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271882462733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_10 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83729320424371 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135943234753 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨10, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83729320424371 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1135943234753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_11 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (4184727075761 / 5000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271890451069 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨11, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (4184727075761 / 5000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271890451069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_12 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83659787256367 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271894472271 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨12, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83659787256367 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271894472271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_13 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (3345002304521 / 4000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271898481613 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨13, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (3345002304521 / 4000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271898481613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_14 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83590352550589 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567975621343 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨14, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83590352550589 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (567975621343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_15 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83555672034633 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271906489579 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨15, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83555672034633 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271906489579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_16 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83521016030911 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271910441853 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨16, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83521016030911 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271910441853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_17 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (16697276901071 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (141994654003 / 6250000000000 : ℝ))
      (E := (cell12538 ⟨17, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (16697276901071 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (141994654003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_18 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (83451777424073 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271918445099 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨18, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (83451777424073 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2271918445099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_19 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (20854298688337 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283990306029 / 12500000000000 : ℝ))
      (E := (cell12538 ⟨19, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (20854298688337 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (283990306029 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12539_0 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16815691509053 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271717407923 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨0, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16815691509053 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271717407923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_1 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (84043430505603 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271721367497 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨1, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (84043430505603 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271721367497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_2 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (672067427791 / 800000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271725403271 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨2, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (672067427791 / 800000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271725403271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_3 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41986725706709 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (227172935093 / 10000000000000 : ℝ))
      (E := (cell12539 ⟨3, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41986725706709 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (227172935093 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_4 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83938499287759 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567933348237 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨4, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83938499287759 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567933348237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_5 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83903572060621 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (17747948159 / 781250000000 : ℝ))
      (E := (cell12539 ⟨5, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83903572060621 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (17747948159 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_6 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16773733939183 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135870694653 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨6, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16773733939183 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135870694653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_7 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83833792157743 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283968170009 / 12500000000000 : ℝ))
      (E := (cell12539 ⟨7, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83833792157743 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283968170009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_8 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16759787882079 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271749342413 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨8, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16759787882079 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271749342413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_9 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20941027854587 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271753343929 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨9, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20941027854587 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271753343929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_10 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83729308146267 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135878685983 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨10, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83729308146267 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135878685983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_11 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83694529558999 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271761375569 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨11, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83694529558999 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271761375569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_12 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (10457471952697 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271765361511 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨12, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (10457471952697 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271765361511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_13 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83625046299213 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135884668159 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨13, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83625046299213 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135884668159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_14 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (16718068311461 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271773364391 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨14, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (16718068311461 / 20000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271773364391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_15 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20888915340357 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135888667769 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨15, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20888915340357 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135888667769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_16 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83521005677337 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271781313643 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨16, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83521005677337 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271781313643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_17 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83486374470963 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271785362439 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨17, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83486374470963 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271785362439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_18 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (325983467611 / 390625000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135894656323 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨18, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (325983467611 / 390625000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135894656323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_19 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (83417185355981 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135896671947 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨19, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (83417185355981 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135896671947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12540_0 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (84078442025707 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271588301241 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨0, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (84078442025707 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271588301241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_1 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (42021707656233 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567898083247 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨1, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (42021707656233 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567898083247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_2 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (42004206803349 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135798163041 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨2, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (42004206803349 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135798163041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_3 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83973436871739 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271600289663 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨3, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83973436871739 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271600289663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_4 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41969242535559 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271604290497 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨4, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41969242535559 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271604290497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_5 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41951779084279 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271608279363 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨5, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41951779084279 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271608279363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_6 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20967164031993 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (141975766539 / 6250000000000 : ℝ))
      (E := (cell12540 ⟨6, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20967164031993 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (141975766539 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_7 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41916889456731 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454323262469 / 20000000000000 : ℝ))
      (E := (cell12540 ⟨7, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41916889456731 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454323262469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_8 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83798926489321 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567905078621 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨8, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83798926489321 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567905078621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_9 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (3350563952801 / 4000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567906069643 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨9, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (3350563952801 / 4000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567906069643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_10 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83729295870241 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271628269909 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨10, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83729295870241 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271628269909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_11 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (5230907350301 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283954036949 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨11, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (5230907350301 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283954036949 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_12 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16731952797757 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567909076097 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨12, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16731952797757 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567909076097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_13 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83625034987361 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283955037853 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨13, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83625034987361 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283955037853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_14 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41795165282971 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (90865771887 / 4000000000000 : ℝ))
      (E := (cell12540 ⟨14, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41795165282971 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (90865771887 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_15 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16711130138021 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227164829347 / 10000000000000 : ℝ))
      (E := (cell12540 ⟨15, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16711130138021 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227164829347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_16 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20880248831401 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454330459499 / 20000000000000 : ℝ))
      (E := (cell12540 ⟨16, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20880248831401 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454330459499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_17 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41743182219187 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567914064149 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨17, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41743182219187 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567914064149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_18 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (83451757994523 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227166029243 / 10000000000000 : ℝ))
      (E := (cell12540 ⟨18, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (83451757994523 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (227166029243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_19 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41708587980169 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271664293641 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨19, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41708587980169 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271664293641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12541_0 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (84078426508627 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271459305219 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨0, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (84078426508627 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271459305219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_1 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (10505425015221 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271463293591 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨1, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (10505425015221 / 12500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271463293591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_2 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (84008398741919 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271467301889 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨2, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (84008398741919 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271467301889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_3 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83973422332417 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271471281457 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨3, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83973422332417 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271471281457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_4 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41969235428397 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271475299059 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨4, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41969235428397 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271475299059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_5 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83903544278773 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271479247563 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨5, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83903544278773 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271479247563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_6 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83868642562267 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227148325113 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨6, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83868642562267 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227148325113 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_7 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (4191688283569 / 5000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135743629989 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨7, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (4191688283569 / 5000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135743629989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_8 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (16759782714081 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271491281957 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨8, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (16759782714081 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271491281957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_9 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83764086223821 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271495266661 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨9, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83764086223821 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271495266661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_10 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41864641798147 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227149927939 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨10, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41864641798147 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227149927939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_11 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83694505652673 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227150326919 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨11, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83694505652673 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227150326919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_12 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83659752357993 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227150724283 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨12, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83659752357993 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227150724283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_13 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (8362502367747 / 10000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271511264933 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨13, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (8362502367747 / 10000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271511264933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_14 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (167180639153 / 200000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567878806401 / 25000000000000 : ℝ))
      (E := (cell12541 ⟨14, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (167180639153 / 200000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567878806401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_15 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83555640020663 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (141969952943 / 6250000000000 : ℝ))
      (E := (cell12541 ⟨15, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83555640020663 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (141969952943 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_16 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41760492487857 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283940402363 / 12500000000000 : ℝ))
      (E := (cell12541 ⟨16, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41760492487857 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283940402363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_17 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (83486354407587 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271527262903 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨17, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (83486354407587 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271527262903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_18 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41725874141197 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271531268019 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨18, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41725874141197 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271531268019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_19 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (4170858328321 / 5000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135767619617 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨19, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (4170858328321 / 5000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135767619617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12542_0 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (3363136439761 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227133030427 / 10000000000000 : ℝ))
      (E := (cell12542 ⟨0, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (3363136439761 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227133030427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_1 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (84043384933507 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135667153563 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨1, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (84043384933507 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135667153563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_2 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (84008383879537 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567834568213 / 25000000000000 : ℝ))
      (E := (cell12542 ⟨2, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (84008383879537 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567834568213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_3 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83973407795453 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271342268447 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨3, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83973407795453 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271342268447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_4 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83938456644787 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271346302859 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨4, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83938456644787 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271346302859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_5 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (2621985324727 / 3125000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135675134477 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨5, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (2621985324727 / 3125000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135675134477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_6 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83868628998799 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227135429089 / 10000000000000 : ℝ))
      (E := (cell12542 ⟨6, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83868628998799 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (227135429089 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_7 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (16766750486299 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271358260929 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨7, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (16766750486299 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271358260929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_8 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83798900653647 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567840575703 / 25000000000000 : ℝ))
      (E := (cell12542 ⟨8, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83798900653647 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567840575703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_9 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (16752814725947 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271366250191 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨9, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (16752814725947 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271366250191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_10 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (3349170852977 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454274056871 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨10, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (3349170852977 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454274056871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_11 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (10461811712821 / 12500000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271374296363 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨11, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (10461811712821 / 12500000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271374296363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_12 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (209149351823 / 250000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454275658597 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨12, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (209149351823 / 250000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454275658597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_13 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83625012369537 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271382280747 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨13, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83625012369537 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271382280747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_14 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41795154294489 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271386265921 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨14, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41795154294489 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271386265921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_15 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41777814676551 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271390254537 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨15, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41777814676551 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271390254537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_16 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (16704194925533 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283924281547 / 12500000000000 : ℝ))
      (E := (cell12542 ⟨16, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (16704194925533 / 20000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283924281547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_17 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41743172189301 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (141962391561 / 6250000000000 : ℝ))
      (E := (cell12542 ⟨17, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41743172189301 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (141962391561 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_18 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (83451738572027 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454280447883 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨18, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (83451738572027 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454280447883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_19 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (3336686286969 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271406238913 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨19, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (3336686286969 / 4000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271406238913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12543_0 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (840783954819 / 1000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227120135619 / 10000000000000 : ℝ))
      (E := (cell12543 ⟨0, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (840783954819 / 1000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227120135619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_1 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (42021684873841 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271205373597 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨1, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (42021684873841 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271205373597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_2 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (84008369019551 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135604677327 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨2, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (84008369019551 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135604677327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_3 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (16794678652169 / 20000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454242673273 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨3, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (16794678652169 / 20000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454242673273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_4 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83938442435097 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271217359787 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨4, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83938442435097 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271217359787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_5 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83903516506033 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454244268707 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨5, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83903516506033 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454244268707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_6 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83868615437567 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271225325973 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨6, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83868615437567 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271225325973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_7 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83833739193807 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271229373159 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨7, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83833739193807 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271229373159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_8 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41899443869523 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271233319071 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨8, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41899443869523 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271233319071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_9 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41882030518883 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283904668147 / 12500000000000 : ℝ))
      (E := (cell12543 ⟨9, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41882030518883 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283904668147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_10 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41864629527317 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271241342833 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨10, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41864629527317 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271241342833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_11 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41847240877251 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271245319061 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨11, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41847240877251 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271245319061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_12 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41829864551203 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271249338707 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨12, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41829864551203 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271249338707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_13 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (20906250265891 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454250670053 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨13, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (20906250265891 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454250670053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_14 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (5224393600211 / 6250000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135628650943 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨14, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (5224393600211 / 6250000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135628650943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_15 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (4177780934371 / 5000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271261315819 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨15, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (4177780934371 / 5000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271261315819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_16 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (5220060267591 / 6250000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135632669873 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨16, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (5220060267591 / 6250000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135632669873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_17 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83486334351419 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227126932101 / 10000000000000 : ℝ))
      (E := (cell12543 ⟨17, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83486334351419 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (227126932101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_18 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41725864431711 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567818330763 / 25000000000000 : ℝ))
      (E := (cell12543 ⟨18, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41725864431711 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567818330763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_19 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (83417147783753 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (56781933773 / 2500000000000 : ℝ))
      (E := (cell12543 ⟨19, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (83417147783753 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (56781933773 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12544_0 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (84078379972251 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271072460981 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨0, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (84078379972251 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271072460981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_1 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (42021677282147 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271076493001 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨1, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (42021677282147 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271076493001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_2 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (42004177080981 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (141942530591 / 6250000000000 : ℝ))
      (E := (cell12544 ⟨2, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (42004177080981 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (141942530591 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_3 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83973378728593 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271084459483 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨3, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83973378728593 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271084459483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_4 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83938428227723 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271088469843 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨4, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83938428227723 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271088469843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_5 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83903502623077 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271092471311 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨5, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83903502623077 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271092471311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_6 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20967150469643 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271096472247 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨6, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20967150469643 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271096472247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_7 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16766745191663 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135550240377 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨7, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16766745191663 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135550240377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_8 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41899437413301 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271104446697 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨8, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41899437413301 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271104446697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_9 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41882024223957 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271108435607 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨9, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41882024223957 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271108435607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_10 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (2093231169673 / 2500000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (90844498193 / 4000000000000 : ℝ))
      (E := (cell12544 ⟨10, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (2093231169673 / 2500000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (90844498193 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_11 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83694469808473 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227111645339 / 10000000000000 : ℝ))
      (E := (cell12544 ⟨11, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83694469808473 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227111645339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_12 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83659717477609 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (283890054759 / 12500000000000 : ℝ))
      (E := (cell12544 ⟨12, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83659717477609 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (283890054759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_13 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83624989759549 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (70972637981 / 3125000000000 : ℝ))
      (E := (cell12544 ⟨13, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83624989759549 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (70972637981 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_14 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20897571654923 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454225689949 / 20000000000000 : ℝ))
      (E := (cell12544 ⟨14, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20897571654923 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454225689949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_15 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83555608023619 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454226486187 / 20000000000000 : ℝ))
      (E := (cell12544 ⟨15, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83555608023619 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454226486187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_16 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (1305014905267 / 1562500000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567784105711 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨16, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (1305014905267 / 1562500000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567784105711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_17 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (83486324326037 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135570215503 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨17, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (83486324326037 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135570215503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_18 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (4172585957829 / 5000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271144460713 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨18, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (4172585957829 / 5000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271144460713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_19 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16683427679001 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (283893557347 / 12500000000000 : ℝ))
      (E := (cell12544 ⟨19, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16683427679001 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (283893557347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12545_0 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (42039182232539 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270943618643 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨0, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (42039182232539 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270943618643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_1 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (42021669691671 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567736901881 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨1, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (42021669691671 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567736901881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_2 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (5250521206673 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135475809709 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨2, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (5250521206673 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135475809709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_3 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83973364198697 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135477802833 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨3, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83973364198697 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135477802833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_4 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (10492301752833 / 12500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270959633029 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨4, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (10492301752833 / 12500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270959633029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_5 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83903488742397 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270963594369 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨5, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83903488742397 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270963594369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_6 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20967147080453 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135483806923 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨6, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20967147080453 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135483806923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_7 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83833712725019 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70967861991 / 3125000000000 : ℝ))
      (E := (cell12545 ⟨7, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83833712725019 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70967861991 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_8 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83798861916313 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270975627711 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨8, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83798861916313 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270975627711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_9 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41882017930089 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70968111859 / 3125000000000 : ℝ))
      (E := (cell12545 ⟨9, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41882017930089 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70968111859 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_10 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41864617260641 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270983620333 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨10, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41864617260641 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270983620333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_11 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (523090361653 / 625000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270987583247 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨11, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (523090361653 / 625000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270987583247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_12 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83659705854811 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270991591079 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨12, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83659705854811 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2270991591079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_13 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20906244614373 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567748898081 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨13, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20906244614373 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567748898081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_14 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83590275637927 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567749898313 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨14, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83590275637927 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567749898313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_15 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83555597361697 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135501799943 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨15, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83555597361697 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135501799943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_16 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (261002948733 / 312500000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (227100761801 / 10000000000000 : ℝ))
      (E := (cell12545 ⟨16, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (261002948733 / 312500000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (227100761801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_17 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (10435789287807 / 12500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567752898741 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨17, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (10435789287807 / 12500000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567752898741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_18 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83451709451499 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454203118837 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨18, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83451709451499 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454203118837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_19 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (83417129007979 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271019562481 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨19, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (83417129007979 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271019562481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12546_0 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (4203917448019 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (113540741459 / 5000000000000 : ℝ))
      (E := (cell12546 ⟨0, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (4203917448019 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (113540741459 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_1 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (3361732968193 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270818832803 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨1, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (3361732968193 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270818832803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_2 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (84008324453969 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270822802383 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨2, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (84008324453969 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270822802383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_3 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (20993337417789 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567706701229 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨3, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (20993337417789 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567706701229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_4 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83938399819921 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135415395729 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨4, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83938399819921 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135415395729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_5 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (10487934357999 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454166965707 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨5, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (10487934357999 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454166965707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_6 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (10483571845911 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (17740928193 / 781250000000 : ℝ))
      (E := (cell12546 ⟨6, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (10483571845911 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (17740928193 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_7 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41916849746959 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454168559591 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨7, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41916849746959 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454168559591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_8 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (4189942450409 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567711701033 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨8, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (4189942450409 / 5000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567711701033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_9 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83764023274557 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (90834031073 / 4000000000000 : ℝ))
      (E := (cell12546 ⟨9, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83764023274557 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (90834031073 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_10 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83729222257721 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270854781329 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨10, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83729222257721 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270854781329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_11 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (3347777836901 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270858824737 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨11, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (3347777836901 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270858824737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_12 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83659694234009 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270862797733 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨12, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83659694234009 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270862797733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_13 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83624967157393 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270866822967 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨13, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83624967157393 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270866822967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_14 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83590264658081 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270870790531 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨14, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83590264658081 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270870790531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_15 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83555586701653 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (227087476453 / 10000000000000 : ℝ))
      (E := (cell12546 ⟨15, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83555586701653 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (227087476453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_16 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (5220058328367 / 6250000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270878808909 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨16, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (5220058328367 / 6250000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270878808909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_17 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (3339452171227 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270882812887 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨17, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (3339452171227 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270882812887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_18 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (83451699748179 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454177356337 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨18, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (83451699748179 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454177356337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_19 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41708559811337 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (56772269463 / 2500000000000 : ℝ))
      (E := (cell12546 ⟨19, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41708559811337 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (56772269463 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12547_0 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (84078333458157 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (227068609259 / 10000000000000 : ℝ))
      (E := (cell12547 ⟨0, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (84078333458157 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (227068609259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_1 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (42021654514371 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270690053203 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨1, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (42021654514371 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270690053203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_2 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16801661920713 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (45413880767 / 2000000000000 : ℝ))
      (E := (cell12547 ⟨2, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16801661920713 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (45413880767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_3 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83973335145969 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135349028617 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨3, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83973335145969 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135349028617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_4 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83938385619491 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270702060909 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨4, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83938385619491 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270702060909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_5 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83903460987861 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270706057987 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨5, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83903460987861 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270706057987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_6 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41934280607499 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283838757103 / 12500000000000 : ℝ))
      (E := (cell12547 ⟨6, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41934280607499 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (283838757103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_7 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20958421566253 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135357032761 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨7, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20958421566253 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135357032761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_8 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41899418051101 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270718033943 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨8, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41899418051101 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270718033943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_9 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20941002672763 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135361013807 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨9, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20941002672763 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135361013807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_10 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16745841999247 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270726053873 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨10, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16745841999247 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270726053873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_11 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16738886796521 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135365030879 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨11, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16738886796521 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135365030879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_12 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83659682615203 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135367029017 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨12, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83659682615203 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135367029017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_13 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (83624955859251 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113536902461 / 5000000000000 : ℝ))
      (E := (cell12547 ⟨13, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (83624955859251 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113536902461 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_14 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (10448781710019 / 12500000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135371020793 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨14, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (10448781710019 / 12500000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135371020793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_15 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (2611111751359 / 3125000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567686510289 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨15, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (2611111751359 / 3125000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567686510289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_16 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41760461457511 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270750053709 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨16, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41760461457511 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270750053709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_17 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41743147130347 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270754026583 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨17, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41743147130347 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270754026583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_18 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (4172584502331 / 5000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135379011607 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨18, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (4172584502331 / 5000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135379011607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_19 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20854277559773 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270762048649 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨19, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20854277559773 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270762048649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12548_0 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (84078317958409 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135278675541 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨0, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (84078317958409 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135278675541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_1 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (84043293855093 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270561384363 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨1, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (84043293855093 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270561384363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_2 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (42004147377777 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90822613093 / 4000000000000 : ℝ))
      (E := (cell12548 ⟨2, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (42004147377777 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (90822613093 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_3 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (2624166269473 / 3125000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270569362623 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨3, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (2624166269473 / 3125000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270569362623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_4 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (671506971371 / 800000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135286662803 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨4, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (671506971371 / 800000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135286662803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_5 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (20975861778501 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270577340637 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨5, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (20975861778501 / 25000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270577340637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_6 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41934273832471 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (17738916861 / 781250000000 : ℝ))
      (E := (cell12548 ⟨6, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41934273832471 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (17738916861 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_7 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (838336730383 / 1000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113529266423 / 5000000000000 : ℝ))
      (E := (cell12548 ⟨7, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (838336730383 / 1000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (113529266423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_8 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41899411599189 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135294658573 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨8, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41899411599189 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135294658573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_9 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41881999054831 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270593331859 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨9, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41881999054831 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270593331859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_10 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (10466149717103 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567649330477 / 25000000000000 : ℝ))
      (E := (cell12548 ⟨10, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (10466149717103 / 12500000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567649330477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_11 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83694422044721 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135300676181 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨11, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83694422044721 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135300676181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_12 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41829835499197 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135302656953 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨12, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41829835499197 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135302656953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_13 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (16724988912613 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135304664593 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨13, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (16724988912613 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135304664593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_14 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (4179512135207 / 5000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (141913334151 / 6250000000000 : ℝ))
      (E := (cell12548 ⟨14, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (4179512135207 / 5000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (141913334151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_15 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (52222228367 / 62500000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135308656739 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨15, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (52222228367 / 62500000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135308656739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_16 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83520912578011 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567655338103 / 25000000000000 : ℝ))
      (E := (cell12548 ⟨16, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83520912578011 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (567655338103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_17 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (5217892765157 / 6250000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135312647123 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨17, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (5217892765157 / 6250000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135312647123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_18 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (83451680346821 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135314659387 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨18, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (83451680346821 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135314659387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_19 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (8341710085723 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (454126662927 / 20000000000000 : ℝ))
      (E := (cell12548 ⟨19, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (8341710085723 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (454126662927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12549_0 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (84078302461133 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270428720247 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨0, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (84078302461133 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270428720247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_1 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (42021639341939 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135216355323 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨1, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (42021639341939 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135216355323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_2 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (84008279909937 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454087333861 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨2, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (84008279909937 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454087333861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_3 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (656041453927 / 781250000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270440663219 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨3, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (656041453927 / 781250000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270440663219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_4 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83938357225573 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141902793833 / 6250000000000 : ℝ))
      (E := (cell12549 ⟨4, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83938357225573 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141902793833 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_5 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (4195171662121 / 5000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270448676489 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨5, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (4195171662121 / 5000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270448676489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_6 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83868534117119 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135226327461 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨6, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83868534117119 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135226327461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_7 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41916829906891 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567614175671 / 25000000000000 : ℝ))
      (E := (cell12549 ⟨7, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41916829906891 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567614175671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_8 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20949702574177 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270460653743 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨8, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20949702574177 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270460653743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_9 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41881992765193 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135232344781 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨9, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41881992765193 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135232344781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_10 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (1308268523117 / 1562500000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454093728693 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨10, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (1308268523117 / 1562500000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454093728693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_11 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (10461801263609 / 12500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (4540945277 / 200000000000 : ℝ))
      (E := (cell12549 ⟨11, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (10461801263609 / 12500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (4540945277 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_12 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (4182982969179 / 5000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (70952396297 / 3125000000000 : ℝ))
      (E := (cell12549 ⟨12, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (4182982969179 / 5000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (70952396297 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_13 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20906233317209 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141905041429 / 6250000000000 : ℝ))
      (E := (cell12549 ⟨13, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20906233317209 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141905041429 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_14 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20897557932511 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135242323451 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨14, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20897557932511 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135242323451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_15 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (8355555473279 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270488639639 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨15, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (8355555473279 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270488639639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_16 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41760451121419 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270492646851 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨16, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41760451121419 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270492646851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_17 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83486274226129 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227049667407 / 10000000000000 : ℝ))
      (E := (cell12549 ⟨17, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83486274226129 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227049667407 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_18 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83451670648781 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270500668367 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨18, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83451670648781 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270500668367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_19 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (83417091477089 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454100926943 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨19, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (83417091477089 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454100926943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

end BstLean.Part268
