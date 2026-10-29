import BstLean.Part268CellShard7Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12525_40 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41348288138959 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568422282543 / 25000000000000 : ℝ))
      (E := (cell12525 ⟨40, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41348288138959 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568422282543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_41 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82662518434377 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (90947725487 / 4000000000000 : ℝ))
      (E := (cell12525 ⟨41, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82662518434377 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (90947725487 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_42 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82628484277473 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273697148801 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨42, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82628484277473 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273697148801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_43 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82594473777381 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136850582259 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨43, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82594473777381 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136850582259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_44 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (3302419476177 / 4000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273705183577 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨44, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (3302419476177 / 4000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273705183577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_45 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82526523629081 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273709146159 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨45, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82526523629081 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273709146159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_46 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20623145980493 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273713168753 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨46, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20623145980493 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273713168753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_47 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20614666938467 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568429283059 / 25000000000000 : ℝ))
      (E := (cell12525 ⟨47, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20614666938467 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (568429283059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_48 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (10303096886961 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136860576379 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨48, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (10303096886961 / 12500000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136860576379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_49 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (2574715809953 / 3125000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136862584807 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨49, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (2574715809953 / 3125000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136862584807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_50 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (41178530096751 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273729180759 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨50, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (41178530096751 / 50000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273729180759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_51 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82323237892061 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273733183931 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨51, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82323237892061 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273733183931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_52 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (8228943898567 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (113686858833 / 5000000000000 : ℝ))
      (E := (cell12525 ⟨52, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (8228943898567 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (113686858833 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_53 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (8225566344597 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273741156261 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨53, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (8225566344597 / 10000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273741156261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_54 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82221911244743 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (22737451789 / 1000000000000 : ℝ))
      (E := (cell12525 ⟨54, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82221911244743 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (22737451789 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_55 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (16437636470783 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273749182457 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨55, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (16437636470783 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273749182457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_56 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (20538619186387 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136876581811 / 50000000000000 : ℝ))
      (E := (cell12525 ⟨56, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (20538619186387 / 25000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (1136876581811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_57 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82120794391847 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273757177999 / 100000000000000 : ℝ))
      (E := (cell12525 ⟨57, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82120794391847 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (2273757177999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_58 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (16417427053031 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284220145347 / 12500000000000 : ℝ))
      (E := (cell12525 ⟨58, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (16417427053031 / 20000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (284220145347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12525_59 : CellCertificate 12525 (891645069291283 / 10000000000000000 : ℝ) (1677007999633111 / 1000000000000000000 : ℝ) (84715679016683 / 2500000000000000 : ℝ)
    (cell12525 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · norm_num [cell12525]
  · have h := gap_lower (n := 12525) (a := (82053499337953 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227376517319 / 10000000000000 : ℝ))
      (E := (cell12525 ⟨59, by decide⟩).energy) (xi := (84715679016683 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12525 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12525]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12525])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12525) (a := (82053499337953 / 100000000000000 : ℝ)) (b := (164483760507 / 100000000000000 : ℝ)) (q := (227376517319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12525])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12525]

theorem cert12526_40 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82696573451249 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273559425953 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨40, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82696573451249 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273559425953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_41 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82662515916899 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136781708967 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨41, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82662515916899 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136781708967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_42 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82628482068759 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136783707621 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨42, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82628482068759 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136783707621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_43 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16518894375401 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273571417343 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨43, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16518894375401 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273571417343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_44 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41280242655981 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273575423487 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨44, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41280242655981 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273575423487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_45 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16505304468821 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (8881169659 / 390625000000 : ℝ))
      (E := (cell12526 ⟨45, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16505304468821 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (8881169659 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_46 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82492582944059 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273583443807 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨46, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82492582944059 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273583443807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_47 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41229333541297 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568396863849 / 25000000000000 : ℝ))
      (E := (cell12526 ⟨47, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41229333541297 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568396863849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_48 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82424774730631 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (45471829317 / 2000000000000 : ℝ))
      (E := (cell12526 ⟨48, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82424774730631 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (45471829317 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_49 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16478181171847 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273595473337 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨49, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16478181171847 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273595473337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_50 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16471412087923 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273599475809 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨50, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16471412087923 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273599475809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_51 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82323238443127 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136801735503 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨51, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82323238443127 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136801735503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_52 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82289439841269 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284200932057 / 12500000000000 : ℝ))
      (E := (cell12526 ⟨52, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82289439841269 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (284200932057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_53 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (20563916151421 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273611429473 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨53, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (20563916151421 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273611429473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_54 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (41110956354077 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136807723111 / 50000000000000 : ℝ))
      (E := (cell12526 ⟨54, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (41110956354077 / 50000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (1136807723111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_55 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (20547046030151 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454723888917 / 20000000000000 : ℝ))
      (E := (cell12526 ⟨55, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (20547046030151 / 25000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454723888917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_56 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (821544788151 / 1000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273623480353 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨56, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (821544788151 / 1000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273623480353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_57 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (16424159352769 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454725498189 / 20000000000000 : ℝ))
      (E := (cell12526 ⟨57, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (16424159352769 / 20000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (454725498189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_58 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82087137939183 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568407868157 / 25000000000000 : ℝ))
      (E := (cell12526 ⟨58, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82087137939183 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (568407868157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12526_59 : CellCertificate 12526 (35664655193979 / 400000000000000 : ℝ) (838437036418731 / 500000000000000000 : ℝ) (338834981430021 / 10000000000000000 : ℝ)
    (cell12526 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · norm_num [cell12526]
  · have h := gap_lower (n := 12526) (a := (82053502313597 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273635480639 / 100000000000000 : ℝ))
      (E := (cell12526 ⟨59, by decide⟩).energy) (xi := (338834981430021 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12526 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12526]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12526])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12526) (a := (82053502313597 / 100000000000000 : ℝ)) (b := (1315763709 / 800000000000 : ℝ)) (q := (2273635480639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12526])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12526]

theorem cert12527_40 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82696570625499 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (18187438217 / 800000000000 : ℝ))
      (E := (cell12527 ⟨40, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82696570625499 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (18187438217 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_41 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41331256700151 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568358438537 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨41, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41331256700151 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568358438537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_42 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82628479860889 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273437795977 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨42, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82628479860889 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273437795977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_43 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16518893995487 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273441784547 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨43, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16518893995487 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273441784547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_44 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41280241860133 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273445777863 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨44, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41280241860133 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273445777863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_45 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82526521059859 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284181221869 / 12500000000000 : ℝ))
      (E := (cell12527 ⟨45, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82526521059859 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (284181221869 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_46 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (41246290983419 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568363443657 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨46, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (41246290983419 / 50000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568363443657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_47 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (3298346656479 / 4000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273457775489 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨47, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (3298346656479 / 4000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273457775489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_48 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (5151548397887 / 6250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273461775913 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨48, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (5151548397887 / 6250000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273461775913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_49 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (10298863225069 / 12500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227346577407 / 10000000000000 : ℝ))
      (E := (cell12527 ⟨49, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (10298863225069 / 12500000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227346577407 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_50 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82357060686269 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568367441977 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨50, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82357060686269 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568367441977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_51 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82323238994697 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (71046054849 / 3125000000000 : ℝ))
      (E := (cell12527 ⟨51, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82323238994697 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (71046054849 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_52 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16457888139467 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227347779239 / 10000000000000 : ℝ))
      (E := (cell12527 ⟨52, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16457888139467 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (227347779239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_53 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82255665765827 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568370439721 / 25000000000000 : ℝ))
      (E := (cell12527 ⟨53, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82255665765827 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (568370439721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_54 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82221914171957 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454697153961 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨54, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82221914171957 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454697153961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_55 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (2568380808989 / 3125000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454697952607 / 20000000000000 : ℝ))
      (E := (cell12527 ⟨55, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (2568380808989 / 3125000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (454697952607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_56 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82154480884969 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273493794363 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨56, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82154480884969 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273493794363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_57 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82120799136123 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136748900603 / 50000000000000 : ℝ))
      (E := (cell12527 ⟨57, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82120799136123 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (1136748900603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_58 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (16417428122691 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273501779833 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨58, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (16417428122691 / 20000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273501779833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12527_59 : CellCertificate 12527 (891587694811633 / 10000000000000000 : ℝ) (1676740167431041 / 1000000000000000000 : ℝ) (169403625706789 / 5000000000000000 : ℝ)
    (cell12527 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · norm_num [cell12527]
  · have h := gap_lower (n := 12527) (a := (82053505289447 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273505785481 / 100000000000000 : ℝ))
      (E := (cell12527 ⟨59, by decide⟩).energy) (xi := (169403625706789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12527 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12527]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12527])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12527) (a := (82053505289447 / 100000000000000 : ℝ)) (b := (164457168913 / 100000000000000 : ℝ)) (q := (2273505785481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12527])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12527]

theorem cert12528_40 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82696567800667 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273300124963 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨40, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82696567800667 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273300124963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_41 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82662510884587 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136652072909 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨41, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82662510884587 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136652072909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_42 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41314238826931 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (90932324587 / 4000000000000 : ℝ))
      (E := (cell12528 ⟨42, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41314238826931 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (90932324587 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_43 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (8259446807867 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568328037133 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨43, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (8259446807867 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568328037133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_44 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41280241064669 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273316129057 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨44, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41280241064669 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273316129057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_45 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41263259888171 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454664034581 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨45, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41263259888171 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454664034581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_46 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20623145247577 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273324161217 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨46, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20623145247577 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273324161217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_47 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (8245866574201 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568332037853 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨47, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (8245866574201 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568332037853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_48 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (1287887093787 / 1562500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273332141869 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨48, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (1287887093787 / 1562500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273332141869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_49 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82390905742449 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568334032689 / 25000000000000 : ℝ))
      (E := (cell12528 ⟨49, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82390905742449 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (568334032689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_50 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (10294632616683 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273340174989 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨50, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (10294632616683 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273340174989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_51 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82323239546771 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273344154397 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨51, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82323239546771 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273344154397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_52 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20572360388467 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273348184463 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨52, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20572360388467 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273348184463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_53 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (51409791829 / 62500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273352144497 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨53, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (51409791829 / 62500000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273352144497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_54 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (82221915636151 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273356149653 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨54, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (82221915636151 / 100000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273356149653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_55 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (10273523456881 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273360196893 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨55, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (10273523456881 / 12500000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273360196893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_56 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (20538620738789 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273364164759 / 100000000000000 : ℝ))
      (E := (cell12528 ⟨56, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (20538620738789 / 25000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (2273364164759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_57 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (41060400754341 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454673633583 / 20000000000000 : ℝ))
      (E := (cell12528 ⟨57, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (41060400754341 / 50000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (454673633583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_58 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (8208714328797 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136686101351 / 50000000000000 : ℝ))
      (E := (cell12528 ⟨58, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (8208714328797 / 10000000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (1136686101351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12528_59 : CellCertificate 12528 (178311802835339 / 2000000000000000 : ℝ) (838303141704361 / 500000000000000000 : ℝ) (338779526016131 / 10000000000000000 : ℝ)
    (cell12528 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · norm_num [cell12528]
  · have h := gap_lower (n := 12528) (a := (2564172133297 / 3125000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (227337620607 / 10000000000000 : ℝ))
      (E := (cell12528 ⟨59, by decide⟩).energy) (xi := (338779526016131 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12528 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12528]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12528])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12528) (a := (2564172133297 / 3125000000000 : ℝ)) (b := (164443876369 / 100000000000000 : ℝ)) (q := (227337620607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12528])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12528]

theorem cert12529_40 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (16539312995351 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273170586923 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨40, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (16539312995351 / 20000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273170586923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_41 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82662508369751 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454634918589 / 20000000000000 : ℝ))
      (E := (cell12529 ⟨41, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82662508369751 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (454634918589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_42 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82628475447677 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227317854767 / 10000000000000 : ℝ))
      (E := (cell12529 ⟨42, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82628475447677 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (227317854767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_43 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (8259446618071 / 10000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273182568097 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨43, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (8259446618071 / 10000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273182568097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_44 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (10320060067397 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (14207416217 / 625000000000 : ℝ))
      (E := (cell12529 ⟨44, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (10320060067397 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (14207416217 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_45 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41263259246777 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273190567717 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨45, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41263259246777 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273190567717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_46 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82492580014471 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273194544701 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨46, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82492580014471 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273194544701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_47 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82458665072699 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568299645791 / 25000000000000 : ℝ))
      (E := (cell12529 ⟨47, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82458665072699 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568299645791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_48 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82424773639161 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273202563717 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨48, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82424773639161 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273202563717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_49 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20597726421231 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136603301169 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨49, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20597726421231 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136603301169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_50 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82357061181201 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273210579119 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨50, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82357061181201 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273210579119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_51 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20580810024837 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (284151826213 / 12500000000000 : ℝ))
      (E := (cell12529 ⟨51, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20580810024837 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (284151826213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_52 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (20572360602717 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136609286831 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨52, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (20572360602717 / 25000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136609286831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_53 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41127834043701 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273222586311 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨53, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41127834043701 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273222586311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_54 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41110958550369 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136613292881 / 50000000000000 : ℝ))
      (E := (cell12529 ⟨54, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41110958550369 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (1136613292881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_55 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (41094094711401 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568307642227 / 25000000000000 : ℝ))
      (E := (cell12529 ⟨55, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (41094094711401 / 50000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (568307642227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_56 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (4107724251283 / 5000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273234591541 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨56, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (4107724251283 / 5000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273234591541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_57 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82120803881521 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273238591073 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨57, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82120803881521 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273238591073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_58 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (10260893245341 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273242622927 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨58, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (10260893245341 / 12500000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273242622927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12529_59 : CellCertificate 12529 (2228825844859 / 25000000000000 : ℝ) (838236210382693 / 500000000000000000 : ℝ) (169375902618203 / 5000000000000000 : ℝ)
    (cell12529 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · norm_num [cell12529]
  · have h := gap_lower (n := 12529) (a := (82053511241767 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273246624053 / 100000000000000 : ℝ))
      (E := (cell12529 ⟨59, by decide⟩).energy) (xi := (169375902618203 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12529 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12529]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12529])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12529) (a := (82053511241767 / 100000000000000 : ℝ)) (b := (82215292997 / 50000000000000 : ℝ)) (q := (2273246624053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12529])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12529]

theorem cert12530_40 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (516853513461 / 625000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (45460820911 / 2000000000000 : ℝ))
      (E := (cell12530 ⟨40, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (516853513461 / 625000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (45460820911 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_41 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82662505855797 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (90921801471 / 4000000000000 : ℝ))
      (E := (cell12530 ⟨41, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82662505855797 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (90921801471 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_42 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (16525694648467 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136524518093 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨42, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (16525694648467 / 20000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136524518093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_43 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41297232141777 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136526521623 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨43, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41297232141777 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136526521623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_44 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82560478949781 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273057057203 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨44, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82560478949781 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273057057203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_45 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (10315814651437 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454612203647 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨45, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (10315814651437 / 12500000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454612203647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_46 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20623144759831 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273065042827 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨46, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20623144759831 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273065042827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_47 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41229332202021 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568267267687 / 25000000000000 : ℝ))
      (E := (cell12530 ⟨47, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41229332202021 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (568267267687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_48 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (8242477327657 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136536520729 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨48, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (8242477327657 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136536520729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_49 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41195452813989 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454615414187 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨49, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41195452813989 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454615414187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_50 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82357061429479 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273081039267 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨50, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82357061429479 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273081039267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_51 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (8232324065243 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (22730850621 / 1000000000000 : ℝ))
      (E := (cell12530 ⟨51, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (8232324065243 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (22730850621 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_52 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82289443268333 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273089078017 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨52, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82289443268333 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273089078017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_53 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (82255669248833 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284136635541 / 12500000000000 : ℝ))
      (E := (cell12530 ⟨53, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (82255669248833 / 100000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (284136635541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_54 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20555479641429 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273097078137 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨54, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20555479641429 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273097078137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_55 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (8218819119091 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454620211267 / 20000000000000 : ℝ))
      (E := (cell12530 ⟨55, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (8218819119091 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (454620211267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_56 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (41077243548241 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273105074711 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨56, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (41077243548241 / 50000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273105074711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_57 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (1026510078183 / 1250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (56827726767 / 2500000000000 : ℝ))
      (E := (cell12530 ⟨57, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (1026510078183 / 1250000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (56827726767 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_58 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (8208714863773 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136556549831 / 50000000000000 : ℝ))
      (E := (cell12530 ⟨58, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (8208714863773 / 10000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (1136556549831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12530_59 : CellCertificate 12530 (178300333222257 / 2000000000000000 : ℝ) (167633857949591 / 100000000000000000 : ℝ) (33872408907313 / 1000000000000000 : ℝ)
    (cell12530 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · norm_num [cell12530]
  · have h := gap_lower (n := 12530) (a := (20513378554559 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273117098609 / 100000000000000 : ℝ))
      (E := (cell12530 ⟨59, by decide⟩).energy) (xi := (33872408907313 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12530 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12530]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12530])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12530) (a := (20513378554559 / 25000000000000 : ℝ)) (b := (82208648893 / 50000000000000 : ℝ)) (q := (2273117098609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12530])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12530]

theorem cert12531_40 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20674139832921 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568227889893 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨40, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20674139832921 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568227889893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_41 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41331251671361 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (35514305251 / 1562500000000 : ℝ))
      (E := (cell12531 ⟨41, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41331251671361 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (35514305251 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_42 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16525694207567 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272919580223 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨42, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16525694207567 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272919580223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_43 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41297231193601 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272923573979 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨43, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41297231193601 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272923573979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_44 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82560477361153 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568231893833 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨44, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82560477361153 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568231893833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_45 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16505303186033 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272931583311 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨45, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16505303186033 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272931583311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_46 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (20623144516217 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568233884463 / 25000000000000 : ℝ))
      (E := (cell12531 ⟨46, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (20623144516217 / 25000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (568233884463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_47 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82458663736037 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272939555269 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨47, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82458663736037 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272939555269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_48 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16484954582919 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272943575093 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨48, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16484954582919 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272943575093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_49 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (8239090557161 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (71029610517 / 3125000000000 : ℝ))
      (E := (cell12531 ⟨49, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (8239090557161 / 10000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (71029610517 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_50 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82357061678297 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272951555433 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨50, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82357061678297 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272951555433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_51 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16464648241203 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (142059723161 / 6250000000000 : ℝ))
      (E := (cell12531 ⟨51, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16464648241203 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (142059723161 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_52 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (16457888825253 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272959579499 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨52, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (16457888825253 / 20000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272959579499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_53 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82255670410693 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284120447439 / 12500000000000 : ℝ))
      (E := (cell12531 ⟨53, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82255670410693 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (284120447439 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_54 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (41110960015543 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272967567717 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨54, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (41110960015543 / 50000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272967567717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_55 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82188192959373 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272971600087 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨55, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82188192959373 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272971600087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_56 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82154489167621 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272975555163 / 100000000000000 : ℝ))
      (E := (cell12531 ⟨56, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82154489167621 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (2272975555163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_57 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (82120808628039 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136489803369 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨57, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (82120808628039 / 100000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136489803369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_58 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (3283486052519 / 4000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454596714751 / 20000000000000 : ℝ))
      (E := (cell12531 ⟨58, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (3283486052519 / 4000000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (454596714751 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12531_59 : CellCertificate 12531 (891472998678689 / 10000000000000000 : ℝ) (1676204759595177 / 1000000000000000000 : ℝ) (42337047190629 / 1250000000000000 : ℝ)
    (cell12531 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · norm_num [cell12531]
  · have h := gap_lower (n := 12531) (a := (2564172412341 / 3125000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136493785279 / 50000000000000 : ℝ))
      (E := (cell12531 ⟨59, by decide⟩).energy) (xi := (42337047190629 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12531 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12531]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12531])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12531) (a := (2564172412341 / 3125000000000 : ℝ)) (b := (82202005873 / 50000000000000 : ℝ)) (q := (1136493785279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12531])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12531]

theorem cert12532_40 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (3307862260421 / 4000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (71024441531 / 3125000000000 : ℝ))
      (E := (cell12532 ⟨40, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (3307862260421 / 4000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (71024441531 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_41 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82662500830527 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136393045407 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨41, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82662500830527 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136393045407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_42 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82628468834177 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568197530251 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨42, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82628468834177 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568197530251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_43 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (16518892098331 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136397050747 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨43, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (16518892098331 / 20000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136397050747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_44 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (8256047577329 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568199522571 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨44, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (8256047577329 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568199522571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_45 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20631628662391 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136401072623 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨45, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20631628662391 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136401072623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_46 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (2577893034097 / 3125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272806147519 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨46, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (2577893034097 / 3125000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272806147519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_47 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41229331534343 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284101261953 / 12500000000000 : ℝ))
      (E := (cell12532 ⟨47, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41229331534343 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284101261953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_48 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (20606193138309 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454562821141 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨48, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (20606193138309 / 25000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454562821141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_49 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (4119545275791 / 5000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454563623411 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨49, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (4119545275791 / 5000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454563623411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_50 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (10294632740957 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272822127619 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨50, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (10294632740957 / 12500000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272822127619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_51 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82323241760103 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454565227027 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨51, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82323241760103 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454565227027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_52 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41144722492331 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136415068563 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨52, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41144722492331 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136415068563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_53 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82255671572981 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136417065451 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨53, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82255671572981 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136417065451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_54 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82221921496847 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272838113563 / 100000000000000 : ℝ))
      (E := (cell12532 ⟨54, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82221921496847 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (2272838113563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_55 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (8218819472819 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454568428217 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨55, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (8218819472819 / 10000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454568428217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_56 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82154491239077 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284105768889 / 12500000000000 : ℝ))
      (E := (cell12532 ⟨56, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82154491239077 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (284105768889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_57 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82120811001719 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454570028023 / 20000000000000 : ℝ))
      (E := (cell12532 ⟨57, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82120811001719 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (454570028023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_58 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (41043576994231 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568213540879 / 25000000000000 : ℝ))
      (E := (cell12532 ⟨58, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (41043576994231 / 50000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (568213540879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12532_59 : CellCertificate 12532 (3565777342579 / 40000000000000 : ℝ) (1676070961058069 / 1000000000000000000 : ℝ) (338668670590841 / 10000000000000000 : ℝ)
    (cell12532 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · norm_num [cell12532]
  · have h := gap_lower (n := 12532) (a := (82053520171793 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136429079131 / 50000000000000 : ℝ))
      (E := (cell12532 ⟨59, by decide⟩).energy) (xi := (338668670590841 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12532 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12532]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12532])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12532) (a := (82053520171793 / 100000000000000 : ℝ)) (b := (2568605123 / 1562500000000 : ℝ)) (q := (1136429079131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12532])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12532]

theorem cert12533_40 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20674138422571 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272652695081 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨40, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20674138422571 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272652695081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_41 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82662498319211 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (90906268041 / 4000000000000 : ℝ))
      (E := (cell12533 ⟨41, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82662498319211 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (90906268041 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_42 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (258213958223 / 312500000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (227266071731 / 10000000000000 : ℝ))
      (E := (cell12533 ⟨42, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (258213958223 / 312500000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (227266071731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_43 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82594458596911 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136332371699 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨43, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82594458596911 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136332371699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_44 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41280237093097 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568167179927 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨44, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41280237093097 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568167179927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_45 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82526513369691 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568168176011 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨45, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82526513369691 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568168176011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_46 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (8249257611803 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272676754087 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨46, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (8249257611803 / 10000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272676754087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_47 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82458662401989 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568170187677 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨47, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82458662401989 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568170187677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_48 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82424772192491 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136342375567 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨48, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82424772192491 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136342375567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_49 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82390905460609 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272688753523 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨49, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82390905460609 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272688753523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_50 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (20589265544389 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136346377913 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨50, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (20589265544389 / 25000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136346377913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_51 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41161621157347 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (35510886809 / 1562500000000 : ℝ))
      (E := (cell12533 ⟨51, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41161621157347 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (35510886809 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_52 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41144722921763 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (142043796931 / 6250000000000 : ℝ))
      (E := (cell12533 ⟨52, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41144722921763 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (142043796931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_53 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41127836367849 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272704738497 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨53, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41127836367849 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272704738497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_54 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82221922963 / 100000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272708774737 / 100000000000000 : ℝ))
      (E := (cell12533 ⟨54, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82221922963 / 100000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (2272708774737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_55 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (1027352456217 / 1250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568178184603 / 25000000000000 : ℝ))
      (E := (cell12533 ⟨55, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (1027352456217 / 1250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (568178184603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_56 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (1643089866217 / 2000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284089593043 / 12500000000000 : ℝ))
      (E := (cell12533 ⟨56, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (1643089866217 / 2000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (284089593043 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_57 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (41060406687839 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454544145989 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨57, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (41060406687839 / 50000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454544145989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_58 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (82087156664193 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454544950127 / 20000000000000 : ℝ))
      (E := (cell12533 ⟨58, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (82087156664193 / 100000000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (454544950127 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12533_59 : CellCertificate 12533 (891415677008409 / 10000000000000000 : ℝ) (104746073992467 / 62500000000000000 : ℝ) (67728193653857 / 2000000000000000 : ℝ)
    (cell12533 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · norm_num [cell12533]
  · have h := gap_lower (n := 12533) (a := (1025669039361 / 1250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136364371681 / 50000000000000 : ℝ))
      (E := (cell12533 ⟨59, by decide⟩).energy) (xi := (67728193653857 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12533 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12533]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12533])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12533) (a := (1025669039361 / 1250000000000 : ℝ)) (b := (41094361541 / 25000000000000 : ℝ)) (q := (1136364371681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12533])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12533]

theorem cert12534_40 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (1033706885887 / 1250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (22725233753 / 1000000000000 : ℝ))
      (E := (cell12534 ⟨40, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (1033706885887 / 1250000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (22725233753 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_41 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (3306499832351 / 4000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136263683349 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨41, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (3306499832351 / 4000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136263683349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_42 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (16525692885877 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272531369139 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨42, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (16525692885877 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272531369139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_43 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82594456702971 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136267691043 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨43, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82594456702971 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136267691043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_44 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (10320059074983 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272539404781 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨44, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (10320059074983 / 12500000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272539404781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_45 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (16505302418109 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136271688701 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨45, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (16505302418109 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136271688701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_46 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41246287572823 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272547357557 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨46, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41246287572823 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272547357557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_47 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82458661735943 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136275701367 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨47, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82458661735943 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136275701367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_48 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41212385916181 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113627769677 / 5000000000000 : ℝ))
      (E := (cell12534 ⟨48, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41212385916181 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113627769677 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_49 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (3295636216239 / 4000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272559387007 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨49, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (3295636216239 / 4000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272559387007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_50 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (20589265606999 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272563381087 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨50, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (20589265606999 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272563381087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_51 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (20580810717447 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272567373509 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨51, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (20580810717447 / 25000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272567373509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_52 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41144723351427 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272571420811 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨52, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41144723351427 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272571420811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_53 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82255673898843 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136287701149 / 50000000000000 : ℝ))
      (E := (cell12534 ⟨53, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82255673898843 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (1136287701149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_54 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82221924429543 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113628968703 / 5000000000000 : ℝ))
      (E := (cell12534 ⟨54, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82221924429543 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (113628968703 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_55 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (16437639653377 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568145848017 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨55, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (16437639653377 / 20000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568145848017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_56 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (4107724769147 / 5000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272587393967 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨56, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (4107724769147 / 5000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272587393967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_57 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82120815749917 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272591435359 / 100000000000000 : ℝ))
      (E := (cell12534 ⟨57, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82120815749917 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (2272591435359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_58 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (41043579670083 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568148848567 / 25000000000000 : ℝ))
      (E := (cell12534 ⟨58, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (41043579670083 / 50000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (568148848567 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12534_59 : CellCertificate 12534 (222846755692151 / 2500000000000000 : ℝ) (167580342805427 / 100000000000000000 : ℝ) (169306635279547 / 5000000000000000 : ℝ)
    (cell12534 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · norm_num [cell12534]
  · have h := gap_lower (n := 12534) (a := (82053526126173 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (284074930527 / 12500000000000 : ℝ))
      (E := (cell12534 ⟨59, by decide⟩).energy) (xi := (169306635279547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12534 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12534]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12534])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12534) (a := (82053526126173 / 100000000000000 : ℝ)) (b := (82182083311 / 50000000000000 : ℝ)) (q := (284074930527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12534])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12534]

theorem cert12535_40 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82696548052553 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272394052189 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨40, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82696548052553 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272394052189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_41 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41331246649609 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454479617567 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨41, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41331246649609 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454479617567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_42 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82628462228251 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (142025129781 / 6250000000000 : ℝ))
      (E := (cell12535 ⟨42, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82628462228251 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (142025129781 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_43 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41297227404917 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272406076363 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨43, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41297227404917 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272406076363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_44 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82560471014299 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272410086681 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨44, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82560471014299 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272410086681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_45 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (2578953462879 / 3125000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272414106473 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨45, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (2578953462879 / 3125000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272414106473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_46 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (322236617867 / 390625000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136209037837 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨46, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (322236617867 / 390625000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136209037837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_47 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82458661070551 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454484422119 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨47, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82458661070551 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454484422119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_48 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (5151548217053 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454485218369 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨48, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (5151548217053 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454485218369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_49 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41195452675959 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136215038227 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨49, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41195452675959 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136215038227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_50 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (1286829104359 / 1562500000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136217060669 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨50, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (1286829104359 / 1562500000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136217060669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_51 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (10290405428173 / 12500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272438106319 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨51, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (10290405428173 / 12500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272438106319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_52 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82289447562649 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272442087859 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨52, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82289447562649 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272442087859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_53 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (5140979691401 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568111530577 / 25000000000000 : ℝ))
      (E := (cell12535 ⟨53, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (5140979691401 / 6250000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (568111530577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_54 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82221925896477 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284056261089 / 12500000000000 : ℝ))
      (E := (cell12535 ⟨54, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82221925896477 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284056261089 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_55 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (20547050009191 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284056762757 / 12500000000000 : ℝ))
      (E := (cell12535 ⟨55, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (20547050009191 / 25000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (284056762757 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_56 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (41077248727673 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454491619997 / 20000000000000 : ℝ))
      (E := (cell12535 ⟨56, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (41077248727673 / 50000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (454491619997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_57 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (16424163624887 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136231069049 / 50000000000000 : ℝ))
      (E := (cell12535 ⟨57, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (16424163624887 / 20000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (1136231069049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_58 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (82087162016381 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272466094419 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨58, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (82087162016381 / 100000000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272466094419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12535_59 : CellCertificate 12535 (222839593231069 / 2500000000000000 : ℝ) (209458711697169 / 125000000000000000 : ℝ) (338585577459 / 10000000000000 : ℝ)
    (cell12535 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · norm_num [cell12535]
  · have h := gap_lower (n := 12535) (a := (10256691137959 / 12500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272470142469 / 100000000000000 : ℝ))
      (E := (cell12535 ⟨59, by decide⟩).energy) (xi := (338585577459 / 10000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12535 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12535]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12535])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12535) (a := (10256691137959 / 12500000000000 : ℝ)) (b := (41087722311 / 25000000000000 : ℝ)) (q := (2272470142469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12535])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12535]

theorem cert12536_40 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41348272617531 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568066210803 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨40, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41348272617531 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568066210803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_41 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (4133124539527 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (28403360071 / 1250000000000 : ℝ))
      (E := (cell12536 ⟨41, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (4133124539527 / 5000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (28403360071 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_42 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41314230013979 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272272839377 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨42, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41314230013979 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272272839377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_43 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (33037781167 / 40000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568069206557 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨43, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (33037781167 / 40000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568069206557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_44 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82560469429499 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227228082423 / 10000000000000 : ℝ))
      (E := (cell12536 ⟨44, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82560469429499 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (227228082423 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_45 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41263254767219 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272284832407 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨45, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41263254767219 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272284832407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_46 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82492573202949 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568072212391 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨46, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82492573202949 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568072212391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_47 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (8245866040581 / 10000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136146407699 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨47, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (8245866040581 / 10000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136146407699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_48 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82424771113949 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (71009276439 / 3125000000000 : ℝ))
      (E := (cell12536 ⟨48, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82424771113949 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (71009276439 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_49 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41195452649219 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272300821861 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨49, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41195452649219 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272300821861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_50 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (1286829108289 / 1562500000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568076214661 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨50, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (1286829108289 / 1562500000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568076214661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_51 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20580810995371 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (113615441811 / 5000000000000 : ℝ))
      (E := (cell12536 ⟨51, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20580810995371 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (113615441811 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_52 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20572362105727 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272312870067 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨52, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20572362105727 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272312870067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_53 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82255676226417 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272316839489 / 100000000000000 : ℝ))
      (E := (cell12536 ⟨53, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82255676226417 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (2272316839489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_54 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (41110963681901 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136160429817 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨54, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (41110963681901 / 50000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136160429817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_55 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (16437640361399 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (284040608547 / 12500000000000 : ℝ))
      (E := (cell12536 ⟨55, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (16437640361399 / 20000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (284040608547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_56 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (20538624882017 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136164431197 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨56, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (20538624882017 / 25000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136164431197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_57 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82120820499233 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136166419079 / 50000000000000 : ℝ))
      (E := (cell12536 ⟨57, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82120820499233 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (1136166419079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_58 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (82087164692839 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568084212771 / 25000000000000 : ℝ))
      (E := (cell12536 ⟨58, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (82087164692839 / 100000000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (568084212771 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12536_59 : CellCertificate 12536 (445664863737183 / 5000000000000000 : ℝ) (1675535980443607 / 1000000000000000000 : ℝ) (84639472241933 / 2500000000000000 : ℝ)
    (cell12536 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · norm_num [cell12536]
  · have h := gap_lower (n := 12536) (a := (2564172877543 / 3125000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (56808520953 / 2500000000000 : ℝ))
      (E := (cell12536 ⟨59, by decide⟩).energy) (xi := (84639472241933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12536 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12536]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12536])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12536) (a := (2564172877543 / 3125000000000 : ℝ)) (b := (10271100877 / 6250000000000 : ℝ)) (q := (56808520953 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12536])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12536]

theorem cert12537_40 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (10337067802311 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272135630907 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨40, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (10337067802311 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272135630907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_41 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82662488282739 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272139637749 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨41, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82662488282739 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272139637749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_42 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16525691565701 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (227214359901 / 10000000000000 : ℝ))
      (E := (cell12537 ⟨42, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16525691565701 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (227214359901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_43 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82594451025969 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454429526337 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨43, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82594451025969 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454429526337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_44 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (10320058480683 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136075808717 / 50000000000000 : ℝ))
      (E := (cell12537 ⟨44, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (10320058480683 / 12500000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136075808717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_45 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (20631627064369 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272155614057 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨45, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (20631627064369 / 25000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272155614057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_46 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16498514446527 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272159620361 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨46, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16498514446527 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272159620361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_47 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41229329870861 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (284020454367 / 12500000000000 : ℝ))
      (E := (cell12537 ⟨47, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41229329870861 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (284020454367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_48 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16484954151133 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136083828077 / 50000000000000 : ℝ))
      (E := (cell12537 ⟨48, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16484954151133 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (1136083828077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_49 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (2574715788923 / 3125000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (35502681613 / 1562500000000 : ℝ))
      (E := (cell12537 ⟨49, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (2574715788923 / 3125000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (35502681613 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_50 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16471412636511 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272175651977 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨50, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16471412636511 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272175651977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_51 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16464648907617 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272179622211 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨51, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16464648907617 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272179622211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_52 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (5143090580227 / 6250000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272183649411 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨52, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (5143090580227 / 6250000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272183649411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_53 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41127838695423 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (28402345161 / 1250000000000 : ℝ))
      (E := (cell12537 ⟨53, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41127838695423 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (28402345161 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_54 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (41110964415759 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272191627767 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨54, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (41110964415759 / 50000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272191627767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_55 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82188203577581 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454439126389 / 20000000000000 : ℝ))
      (E := (cell12537 ⟨55, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82188203577581 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (454439126389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_56 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82154501601107 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568049905523 / 25000000000000 : ℝ))
      (E := (cell12537 ⟨56, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82154501601107 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (568049905523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_57 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (8212082287431 / 10000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272203653807 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨57, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (8212082287431 / 10000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272203653807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_58 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (82087167369539 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272207664269 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨58, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (82087167369539 / 100000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272207664269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12537_59 : CellCertificate 12537 (222825271604453 / 2500000000000000 : ℝ) (1675402288647927 / 1000000000000000000 : ℝ) (42316275635503 / 1250000000000000 : ℝ)
    (cell12537 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · norm_num [cell12537]
  · have h := gap_lower (n := 12537) (a := (16410707011857 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272211649531 / 100000000000000 : ℝ))
      (E := (cell12537 ⟨59, by decide⟩).energy) (xi := (42316275635503 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12537 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12537]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12537])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12537) (a := (16410707011857 / 20000000000000 : ℝ)) (b := (82162170491 / 50000000000000 : ℝ)) (q := (2272211649531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12537])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12537]

theorem cert12538_40 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (8269653960283 / 10000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454401294801 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨40, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (8269653960283 / 10000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454401294801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_41 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41331242887909 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136005233263 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨41, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41331242887909 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136005233263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_42 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82628455629893 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272014472949 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨42, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82628455629893 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272014472949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_43 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (2064861228381 / 2500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272018433929 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨43, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (2064861228381 / 2500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272018433929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_44 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (16512093252439 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (142001404143 / 6250000000000 : ℝ))
      (E := (cell12538 ⟨44, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (16512093252439 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (142001404143 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_45 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (2063162674531 / 2500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272026451421 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨45, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (2063162674531 / 2500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272026451421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_46 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (8249257126301 / 10000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454406089387 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨46, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (8249257126301 / 10000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454406089387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_47 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (16491731815657 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272034451417 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨47, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (16491731815657 / 20000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272034451417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_48 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41212385198997 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272038463241 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨48, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41212385198997 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272038463241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_49 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82390905193211 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454408496113 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨49, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82390905193211 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454408496113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_50 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41178531717577 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272046442367 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨50, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41178531717577 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272046442367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_51 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (20580811273797 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (71001577009 / 3125000000000 : ℝ))
      (E := (cell12538 ⟨51, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (20580811273797 / 25000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (71001577009 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_52 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82289450144821 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136027242451 / 50000000000000 : ℝ))
      (E := (cell12538 ⟨52, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82289450144821 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (1136027242451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_53 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41127839277851 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272058501519 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨53, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41127839277851 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272058501519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_54 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (10277741287453 / 12500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (568015613043 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨54, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (10277741287453 / 12500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (568015613043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_55 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (82188205348519 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (568016627733 / 25000000000000 : ℝ))
      (E := (cell12538 ⟨55, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (82188205348519 / 100000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (568016627733 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_56 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41077251837231 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272070497291 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨56, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41077251837231 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272070497291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_57 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41060412624833 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (113603723339 / 5000000000000 : ℝ))
      (E := (cell12538 ⟨57, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41060412624833 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (113603723339 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_58 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (41043585023241 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454415694963 / 20000000000000 : ℝ))
      (E := (cell12538 ⟨58, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (41043585023241 / 50000000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (454415694963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12538_59 : CellCertificate 12538 (445636224876779 / 5000000000000000 : ℝ) (418817154546301 / 250000000000000000 : ℝ) (169251262903303 / 5000000000000000 : ℝ)
    (cell12538 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · norm_num [cell12538]
  · have h := gap_lower (n := 12538) (a := (410267690187 / 500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272082517519 / 100000000000000 : ℝ))
      (E := (cell12538 ⟨59, by decide⟩).energy) (xi := (169251262903303 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12538 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12538]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12538])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12538) (a := (410267690187 / 500000000000 : ℝ)) (b := (164311070097 / 100000000000000 : ℝ)) (q := (2272082517519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12538])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12538]

theorem cert12539_40 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (10337067098511 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271877313777 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨40, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (10337067098511 / 12500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271877313777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_41 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41331241634887 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567970337693 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨41, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41331241634887 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567970337693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_42 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82628453432121 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271885343639 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨42, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82628453432121 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271885343639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_43 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41297223622657 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271889350569 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨43, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41297223622657 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271889350569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_44 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82560464679689 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271893311973 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨44, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82560464679689 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271893311973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_45 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82526505705731 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271897344503 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨45, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82526505705731 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271897344503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_46 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (3299702811763 / 4000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271901329287 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨46, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (3299702811763 / 4000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271901329287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_47 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82458658415501 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135952661869 / 50000000000000 : ℝ))
      (E := (cell12539 ⟨47, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82458658415501 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (1135952661869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_48 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41212385020469 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271909326231 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨48, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41212385020469 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271909326231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_49 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41195452570731 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (56797833373 / 2500000000000 : ℝ))
      (E := (cell12539 ⟨49, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41195452570731 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (56797833373 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_50 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (20589265922073 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271917347751 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨50, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (20589265922073 / 25000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271917347751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_51 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41161622826397 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567980340613 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨51, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41161622826397 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567980340613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_52 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (3291578040259 / 4000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (70997668017 / 3125000000000 : ℝ))
      (E := (cell12539 ⟨52, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (3291578040259 / 4000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (70997668017 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_53 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41127839860493 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567982346833 / 25000000000000 : ℝ))
      (E := (cell12539 ⟨53, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41127839860493 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (567982346833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_54 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (2055548294203 / 2500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283991673989 / 12500000000000 : ℝ))
      (E := (cell12539 ⟨54, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (2055548294203 / 2500000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (283991673989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_55 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82188207119811 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271937387169 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨55, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82188207119811 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271937387169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_56 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82154505748133 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (113597068489 / 5000000000000 : ℝ))
      (E := (cell12539 ⟨56, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82154505748133 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (113597068489 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_57 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82120827625301 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (141996587209 / 6250000000000 : ℝ))
      (E := (cell12539 ⟨57, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82120827625301 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (141996587209 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_58 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (41043586361833 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271949401037 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨58, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (41043586361833 / 50000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271949401037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12539_59 : CellCertificate 12539 (27851369296267 / 312500000000000 : ℝ) (418783742262583 / 250000000000000000 : ℝ) (338474851134213 / 10000000000000000 : ℝ)
    (cell12539 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · norm_num [cell12539]
  · have h := gap_lower (n := 12539) (a := (82053541015719 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271953382911 / 100000000000000 : ℝ))
      (E := (cell12539 ⟨59, by decide⟩).energy) (xi := (338474851134213 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12539 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12539]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12539])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12539) (a := (82053541015719 / 100000000000000 : ℝ)) (b := (82148900687 / 50000000000000 : ℝ)) (q := (2271953382911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12539])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12539]

theorem cert12540_40 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82696533974261 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283968533461 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨40, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82696533974261 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283968533461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_41 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82662480764607 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283969036311 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨41, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82662480764607 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283969036311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_42 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20657112808797 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135878134931 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨42, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20657112808797 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135878134931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_43 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (8259444535619 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271760263999 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨43, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (8259444535619 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271760263999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_44 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20640115774487 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (113588213607 / 5000000000000 : ℝ))
      (E := (cell12540 ⟨44, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20640115774487 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (113588213607 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_45 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82526504430949 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271768293303 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨45, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82526504430949 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271768293303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_46 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20623142331457 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (113588613371 / 5000000000000 : ℝ))
      (E := (cell12540 ⟨46, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20623142331457 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (113588613371 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_47 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82458657753367 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271776251903 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨47, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82458657753367 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271776251903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_48 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (5151548105281 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567945076011 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨48, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (5151548105281 / 6250000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567945076011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_49 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (8239090509029 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283973038023 / 12500000000000 : ℝ))
      (E := (cell12540 ⟨49, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (8239090509029 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (283973038023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_50 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (8235706394197 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135894154581 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨50, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (8235706394197 / 10000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135894154581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_51 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82323246210901 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271792257717 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨51, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82323246210901 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271792257717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_52 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (82289451868593 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271796265323 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨52, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (82289451868593 / 100000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271796265323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_53 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (10281960110837 / 12500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271800270321 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨53, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (10281960110837 / 12500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271800270321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_54 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (41110966618503 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567951067451 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨54, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (41110966618503 / 50000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567951067451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_55 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16437641778291 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271808319743 / 100000000000000 : ℝ))
      (E := (cell12540 ⟨55, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16437641778291 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (2271808319743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_56 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (2053862695553 / 2500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135906149333 / 50000000000000 : ℝ))
      (E := (cell12540 ⟨56, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (2053862695553 / 2500000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (1135906149333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_57 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (16424166000243 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454363264247 / 20000000000000 : ℝ))
      (E := (cell12540 ⟨57, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (16424166000243 / 20000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (454363264247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_58 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20521793850273 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (141988770289 / 6250000000000 : ℝ))
      (E := (cell12540 ⟨58, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20521793850273 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (141988770289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12540_59 : CellCertificate 12540 (891215189597711 / 10000000000000000 : ℝ) (1675001341238207 / 1000000000000000000 : ℝ) (338447181065577 / 10000000000000000 : ℝ)
    (cell12540 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · norm_num [cell12540]
  · have h := gap_lower (n := 12540) (a := (20513385998561 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567956076221 / 25000000000000 : ℝ))
      (E := (cell12540 ⟨59, by decide⟩).energy) (xi := (338447181065577 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12540 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12540]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12540])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12540) (a := (20513385998561 / 25000000000000 : ℝ)) (b := (164284534813 / 100000000000000 : ℝ)) (q := (567956076221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12540])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12540]

theorem cert12541_40 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (1653930623227 / 2000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (90864768731 / 4000000000000 : ℝ))
      (E := (cell12541 ⟨40, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (1653930623227 / 2000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (90864768731 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_41 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82662478260319 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135811613459 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨41, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82662478260319 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135811613459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_42 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (16525689807819 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271627251617 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨42, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (16525689807819 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271627251617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_43 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82594443467867 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135815616513 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨43, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82594443467867 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135815616513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_44 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82560461516971 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271635229137 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨44, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82560461516971 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271635229137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_45 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41263251578447 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567909809743 / 25000000000000 : ℝ))
      (E := (cell12541 ⟨45, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41263251578447 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567909809743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_46 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82492568358271 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271643261333 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨46, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82492568358271 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271643261333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_47 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (16491731418377 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227164723591 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨47, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (16491731418377 / 20000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227164723591 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_48 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82424769328667 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567912819711 / 25000000000000 : ℝ))
      (E := (cell12541 ⟨48, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82424769328667 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (567912819711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_49 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41195452519847 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283956908809 / 12500000000000 : ℝ))
      (E := (cell12541 ⟨49, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41195452519847 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (283956908809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_50 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41178532098093 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (454331853527 / 20000000000000 : ℝ))
      (E := (cell12541 ⟨50, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41178532098093 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (454331853527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_51 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (8232324676951 / 10000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135831634031 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨51, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (8232324676951 / 10000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135831634031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_52 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (3291578109247 / 4000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227166726927 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨52, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (3291578109247 / 4000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227166726927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_53 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41127841026417 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135835634281 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨53, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41127841026417 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135835634281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_54 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82221934706281 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135837631517 / 50000000000000 : ℝ))
      (E := (cell12541 ⟨54, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82221934706281 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (1135837631517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_55 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (20547052665863 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227167924957 / 10000000000000 : ℝ))
      (E := (cell12541 ⟨55, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (20547052665863 / 25000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (227167924957 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_56 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (41077254948211 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (141980205247 / 6250000000000 : ℝ))
      (E := (cell12541 ⟨56, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (41077254948211 / 50000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (141980205247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_57 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82120832377407 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271687303587 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨57, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82120832377407 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271687303587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_58 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (2052179451969 / 2500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271691304733 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨58, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (2052179451969 / 2500000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271691304733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12541_59 : CellCertificate 12541 (445593283052001 / 5000000000000000 : ℝ) (1674867734743727 / 1000000000000000000 : ℝ) (338419515599433 / 10000000000000000 : ℝ)
    (cell12541 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · norm_num [cell12541]
  · have h := gap_lower (n := 12541) (a := (82053546972973 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271695283441 / 100000000000000 : ℝ))
      (E := (cell12541 ⟨59, by decide⟩).energy) (xi := (338419515599433 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12541 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12541]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12541])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12541) (a := (82053546972973 / 100000000000000 : ℝ)) (b := (164271270413 / 100000000000000 : ℝ)) (q := (2271695283441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12541])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12541]

theorem cert12542_40 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41348264174677 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135745141501 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨40, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41348264174677 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135745141501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_41 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82662475756907 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135747138787 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨41, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82662475756907 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135747138787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_42 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41314223421921 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283937286113 / 12500000000000 : ℝ))
      (E := (cell12542 ⟨42, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41314223421921 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (283937286113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_43 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41297220790173 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135751128823 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨43, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41297220790173 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135751128823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_44 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41280229968379 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271506241791 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨44, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41280229968379 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271506241791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_45 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (20631625470891 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271510240361 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨45, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (20631625470891 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271510240361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_46 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41246283695701 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454302850431 / 20000000000000 : ℝ))
      (E := (cell12542 ⟨46, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41246283695701 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (454302850431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_47 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41229328215527 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271518275761 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨47, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41229328215527 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271518275761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_48 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (20606192243363 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567880562657 / 25000000000000 : ℝ))
      (E := (cell12542 ⟨48, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (20606192243363 / 25000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567880562657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_49 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41195452494837 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271526292727 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨49, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41195452494837 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271526292727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_50 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (4117853222547 / 5000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271530282139 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨50, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (4117853222547 / 5000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271530282139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_51 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (4116162366431 / 5000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567883568877 / 25000000000000 : ℝ))
      (E := (cell12542 ⟨51, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (4116162366431 / 5000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (567883568877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_52 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82289453594221 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135769135177 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨52, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82289453594221 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135769135177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_53 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82255683219399 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271542263979 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨53, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82255683219399 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271542263979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_54 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82221936175947 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271546312539 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨54, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82221936175947 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271546312539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_55 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41094106217901 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271550294817 / 100000000000000 : ℝ))
      (E := (cell12542 ⟨55, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41094106217901 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (2271550294817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_56 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (513465699819 / 625000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (70986070829 / 3125000000000 : ℝ))
      (E := (cell12542 ⟨56, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (513465699819 / 625000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (70986070829 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_57 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (41060417376939 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135779141633 / 50000000000000 : ℝ))
      (E := (cell12542 ⟨57, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (41060417376939 / 50000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (1135779141633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_58 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82087180756669 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (70986321319 / 3125000000000 : ℝ))
      (E := (cell12542 ⟨58, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82087180756669 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (70986321319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12542_59 : CellCertificate 12542 (891157946998359 / 10000000000000000 : ℝ) (1674734149561791 / 1000000000000000000 : ℝ) (67678370946903 / 2000000000000000 : ℝ)
    (cell12542 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · norm_num [cell12542]
  · have h := gap_lower (n := 12542) (a := (82053549951907 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (113578315929 / 5000000000000 : ℝ))
      (E := (cell12542 ⟨59, by decide⟩).energy) (xi := (67678370946903 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12542 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12542]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12542])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12542) (a := (82053549951907 / 100000000000000 : ℝ)) (b := (6570320327 / 4000000000000 : ℝ)) (q := (113578315929 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12542])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12542]

theorem cert12543_40 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (2584266423071 / 3125000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283920168051 / 12500000000000 : ℝ))
      (E := (cell12543 ⟨40, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (2584266423071 / 3125000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283920168051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_41 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (20665618313593 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271365324947 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨41, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (20665618313593 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271365324947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_42 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82628444649427 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567842330737 / 25000000000000 : ℝ))
      (E := (cell12543 ⟨42, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82628444649427 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567842330737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_43 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41297219846813 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283921667233 / 12500000000000 : ℝ))
      (E := (cell12543 ⟨43, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41297219846813 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283921667233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_44 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (20640114589327 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454275462021 / 20000000000000 : ℝ))
      (E := (cell12543 ⟨44, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (20640114589327 / 25000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (454275462021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_45 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82526500610961 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (14196133477 / 625000000000 : ℝ))
      (E := (cell12543 ⟨45, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82526500610961 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (14196133477 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_46 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82492566425221 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271385357633 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨46, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82492566425221 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271385357633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_47 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82458655770873 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271389312561 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨47, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82458655770873 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271389312561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_48 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (1648495372377 / 2000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271393337239 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨48, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (1648495372377 / 2000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271393337239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_49 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82390904940229 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283924664001 / 12500000000000 : ℝ))
      (E := (cell12543 ⟨49, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82390904940229 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (283924664001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_50 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41178532353117 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271401352671 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨50, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41178532353117 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271401352671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_51 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82323247888231 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135702669523 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨51, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82323247888231 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135702669523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_52 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82289454457731 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271409327593 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨52, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82289454457731 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271409327593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_53 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (8225568438639 / 10000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (45428267493 / 2000000000000 : ℝ))
      (E := (cell12543 ⟨53, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (8225568438639 / 10000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (45428267493 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_54 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41110968823001 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (113570867963 / 5000000000000 : ℝ))
      (E := (cell12543 ⟨54, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41110968823001 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (113570867963 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_55 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (10273526776063 / 12500000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (56785533433 / 2500000000000 : ℝ))
      (E := (cell12543 ⟨55, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (10273526776063 / 12500000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (56785533433 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_56 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41077257022987 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567856341153 / 25000000000000 : ℝ))
      (E := (cell12543 ⟨56, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41077257022987 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (567856341153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_57 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (82120837130627 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271429378541 / 100000000000000 : ℝ))
      (E := (cell12543 ⟨57, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (82120837130627 / 100000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (2271429378541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_58 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (4104359171741 / 5000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135716687681 / 50000000000000 : ℝ))
      (E := (cell12543 ⟨58, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (4104359171741 / 5000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (1135716687681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12543_59 : CellCertificate 12543 (35645173291189 / 400000000000000 : ℝ) (16746005856873 / 10000000000000000 : ℝ) (8459104961739 / 250000000000000 : ℝ)
    (cell12543 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · norm_num [cell12543]
  · have h := gap_lower (n := 12543) (a := (41026776465523 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (18171498809 / 800000000000 : ℝ))
      (E := (cell12543 ⟨59, by decide⟩).energy) (xi := (8459104961739 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12543 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12543]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12543])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12543) (a := (41026776465523 / 50000000000000 : ℝ)) (b := (164244748097 / 100000000000000 : ℝ)) (q := (18171498809 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12543])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12543]

theorem cert12544_40 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16539304545621 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567808100623 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨40, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16539304545621 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567808100623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_41 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82662470752713 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135618213897 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨41, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82662470752713 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135618213897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_42 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82628442455851 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271240412527 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨42, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82628442455851 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271240412527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_43 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20648609451927 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567811103719 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨43, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20648609451927 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567811103719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_44 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41280228389311 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271248434079 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨44, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41280228389311 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271248434079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_45 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82526499339083 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135626205151 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨45, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82526499339083 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135626205151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_46 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (5155785341233 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271256460023 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨46, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (5155785341233 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271256460023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_47 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (5153665944459 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135630232051 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨47, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (5153665944459 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135630232051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_48 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41212384132431 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135632210419 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨48, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41212384132431 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135632210419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_49 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82390904891361 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135634223101 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨49, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82390904891361 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135634223101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_50 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16471412992413 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271272479237 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨50, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16471412992413 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271272479237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_51 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82323248448343 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135638229339 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨51, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82323248448343 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135638229339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_52 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16457891064341 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135640220493 / 50000000000000 : ℝ))
      (E := (cell12544 ⟨52, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16457891064341 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (1135640220493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_53 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (5140980347113 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271284482499 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨53, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (5140980347113 / 6250000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271284482499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_54 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41110969558223 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (113564423113 / 5000000000000 : ℝ))
      (E := (cell12544 ⟨54, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41110969558223 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (113564423113 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_55 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41094107990779 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271292436163 / 100000000000000 : ℝ))
      (E := (cell12544 ⟨55, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41094107990779 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (2271292436163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_56 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (41077258060611 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227129645999 / 10000000000000 : ℝ))
      (E := (cell12544 ⟨56, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (41077258060611 / 50000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (227129645999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_57 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (16424167901531 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454260094229 / 20000000000000 : ℝ))
      (E := (cell12544 ⟨57, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (16424167901531 / 20000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454260094229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_58 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (20521796528303 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567826116471 / 25000000000000 : ℝ))
      (E := (cell12544 ⟨58, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (20521796528303 / 25000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (567826116471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12544_59 : CellCertificate 12544 (222775180486761 / 2500000000000000 : ℝ) (1674467043115157 / 1000000000000000000 : ℝ) (169168273401651 / 5000000000000000 : ℝ)
    (cell12544 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · norm_num [cell12544]
  · have h := gap_lower (n := 12544) (a := (82053555910389 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454261699887 / 20000000000000 : ℝ))
      (E := (cell12544 ⟨59, by decide⟩).energy) (xi := (169168273401651 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12544 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12544]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12544])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12544) (a := (82053555910389 / 100000000000000 : ℝ)) (b := (164231490179 / 100000000000000 : ℝ)) (q := (454261699887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12544])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12544]

theorem cert12545_40 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20674129979713 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271103574719 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨40, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20674129979713 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271103574719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_41 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82662468251931 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454221517223 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨41, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82662468251931 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454221517223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_42 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41314220131557 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271111616421 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨42, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41314220131557 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271111616421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_43 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (8259443592259 / 10000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (227111560629 / 10000000000000 : ℝ))
      (E := (cell12545 ⟨43, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (8259443592259 / 10000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (227111560629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_44 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41280227600349 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271119613713 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨44, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41280227600349 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271119613713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_45 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (8252649806793 / 10000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283890447357 / 12500000000000 : ℝ))
      (E := (cell12545 ⟨45, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (8252649806793 / 10000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283890447357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_46 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82492564494923 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271127618197 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨46, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82492564494923 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271127618197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_47 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (5153665903279 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135565806297 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨47, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (5153665903279 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135565806297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_48 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41212383955743 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135567809633 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨48, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41212383955743 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135567809633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_49 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20597726210767 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135569788711 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨49, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20597726210767 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135569788711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_50 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (16471413043687 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135571801433 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨50, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (16471413043687 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135571801433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_51 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20580812252239 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567786908601 / 25000000000000 : ℝ))
      (E := (cell12545 ⟨51, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20580812252239 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (567786908601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_52 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (82289456186143 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454230322107 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨52, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (82289456186143 / 100000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454230322107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_53 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (20563921680413 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283894448441 / 12500000000000 : ℝ))
      (E := (cell12545 ⟨53, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (20563921680413 / 25000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (283894448441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_54 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (1027774257341 / 1250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135579810769 / 50000000000000 : ℝ))
      (E := (cell12545 ⟨54, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (1027774257341 / 1250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (1135579810769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_55 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (16437643550993 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454232718269 / 20000000000000 : ℝ))
      (E := (cell12545 ⟨55, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (16437643550993 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (454232718269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_56 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (41077259098393 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271167611769 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨56, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (41077259098393 / 50000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271167611769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_57 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (513255261781 / 625000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271171620213 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨57, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (513255261781 / 625000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271171620213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_58 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (16417437758369 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271175612931 / 100000000000000 : ℝ))
      (E := (cell12545 ⟨58, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (16417437758369 / 20000000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (2271175612931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12545_59 : CellCertificate 12545 (891072115999257 / 10000000000000000 : ℝ) (334866704368053 / 200000000000000000 : ℝ) (169154449867239 / 5000000000000000 : ℝ)
    (cell12545 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · norm_num [cell12545]
  · have h := gap_lower (n := 12545) (a := (5128347430621 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70974363911 / 3125000000000 : ℝ))
      (E := (cell12545 ⟨59, by decide⟩).energy) (xi := (169154449867239 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12545 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12545]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12545])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12545) (a := (5128347430621 / 6250000000000 : ℝ)) (b := (164218234421 / 100000000000000 : ℝ)) (q := (70974363911 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12545])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12545]

theorem cert12546_40 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82696517110513 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270974802361 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨40, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82696517110513 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270974802361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_41 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (3306498630081 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270978799911 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨41, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (3306498630081 / 4000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270978799911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_42 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (16525687614243 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135491408537 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨42, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (16525687614243 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135491408537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_43 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (161317253981 / 195312500000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135493397251 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨43, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (161317253981 / 195312500000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135493397251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_44 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41280226811769 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270990790183 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨44, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41280226811769 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2270990790183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_45 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82526496797503 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454198960627 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨45, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82526496797503 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454198960627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_46 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41246281765403 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567749693321 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨46, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41246281765403 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567749693321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_47 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (16491730758847 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135501408467 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨47, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (16491730758847 / 20000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135501408467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_48 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41212383779361 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567751703671 / 25000000000000 : ℝ))
      (E := (cell12546 ⟨48, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41212383779361 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (567751703671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_49 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (1647818095907 / 2000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271010823559 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨49, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (1647818095907 / 2000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271010823559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_50 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41178532737671 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (227101478253 / 10000000000000 : ℝ))
      (E := (cell12546 ⟨50, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41178532737671 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (227101478253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_51 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82323249570069 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454203761447 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨51, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82323249570069 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454203761447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_52 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (20572364262761 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271022836241 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨52, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (20572364262761 / 25000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271022836241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_53 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41127843944961 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454205361563 / 20000000000000 : ℝ))
      (E := (cell12546 ⟨53, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41127843944961 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (454205361563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_54 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (41110971029251 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135515418549 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨54, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (41110971029251 / 50000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135515418549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_55 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82188219528723 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271034802871 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨55, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82188219528723 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271034802871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_56 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (10269315034083 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271038819953 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨56, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (10269315034083 / 12500000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271038819953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_57 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (5132552766409 / 6250000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135521412873 / 50000000000000 : ℝ))
      (E := (cell12546 ⟨57, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (5132552766409 / 6250000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (1135521412873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_58 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (128261236673 / 156250000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283880852063 / 12500000000000 : ℝ))
      (E := (cell12546 ⟨58, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (128261236673 / 156250000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (283880852063 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12546_59 : CellCertificate 12546 (89104351443531 / 1000000000000000 : ℝ) (1674200021857529 / 1000000000000000000 : ℝ) (169140628630913 / 5000000000000000 : ℝ)
    (cell12546 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · norm_num [cell12546]
  · have h := gap_lower (n := 12546) (a := (82053561869687 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271050847457 / 100000000000000 : ℝ))
      (E := (cell12546 ⟨59, by decide⟩).energy) (xi := (169140628630913 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12546 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12546]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12546])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12546) (a := (82053561869687 / 100000000000000 : ℝ)) (b := (164204980821 / 100000000000000 : ℝ)) (q := (2271050847457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12546])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12546]

theorem cert12547_40 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82696514303087 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567711506671 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨40, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82696514303087 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567711506671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_41 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16532492650599 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270850010427 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨41, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16532492650599 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270850010427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_42 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41314217940077 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135427007243 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨42, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41314217940077 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135427007243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_43 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16518886430951 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270858038313 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨43, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16518886430951 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270858038313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_44 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (4128022602357 / 5000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567715505579 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨44, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (4128022602357 / 5000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567715505579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_45 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (412632477639 / 500000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270866024289 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨45, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (412632477639 / 500000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270866024289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_46 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (5155785160461 / 6250000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270870043031 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨46, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (5155785160461 / 6250000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270870043031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_47 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16491730627331 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135437009113 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨47, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16491730627331 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135437009113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_48 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (20606191801643 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567719516503 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨48, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (20606191801643 / 25000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567719516503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_49 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82390904748207 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567720516681 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨49, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82390904748207 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567720516681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_50 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82357065732787 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567721519299 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨50, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82357065732787 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567721519299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_51 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82323250131683 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270890036161 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨51, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82323250131683 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270890036161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_52 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82289457916407 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567723514773 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨52, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82289457916407 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567723514773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_53 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41127844529309 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (14193113027 / 625000000000 : ℝ))
      (E := (cell12547 ⟨53, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41127844529309 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (14193113027 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_54 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82221943530113 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567725512469 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨54, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82221943530113 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567725512469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_55 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82188221302833 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135453035369 / 50000000000000 : ℝ))
      (E := (cell12547 ⟨55, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82188221302833 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (1135453035369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_56 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (82154522348857 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113545504227 / 5000000000000 : ℝ))
      (E := (cell12547 ⟨56, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (82154522348857 / 100000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (113545504227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_57 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16424169328081 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (35483032621 / 1562500000000 : ℝ))
      (E := (cell12547 ⟨57, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16424169328081 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (35483032621 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_58 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (16417438829967 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567729519151 / 25000000000000 : ℝ))
      (E := (cell12547 ⟨58, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (16417438829967 / 20000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (567729519151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12547_59 : CellCertificate 12547 (445507458627073 / 5000000000000000 : ℝ) (1674066543161859 / 1000000000000000000 : ℝ) (338253619384083 / 10000000000000000 : ℝ)
    (cell12547 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · norm_num [cell12547]
  · have h := gap_lower (n := 12547) (a := (41026782424821 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270922106349 / 100000000000000 : ℝ))
      (E := (cell12547 ⟨59, by decide⟩).energy) (xi := (338253619384083 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12547 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12547]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12547])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12547) (a := (41026782424821 / 50000000000000 : ℝ)) (b := (8209586469 / 5000000000000 : ℝ)) (q := (2270922106349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12547])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12547]

theorem cert12548_40 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (3307860459863 / 4000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135358653211 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨40, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (3307860459863 / 4000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135358653211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_41 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82662460754841 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270721335177 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨41, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82662460754841 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270721335177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_42 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82628433689931 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270725326217 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨42, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82628433689931 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270725326217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_43 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41297215136019 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270729337727 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨43, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41297215136019 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270729337727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_44 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (16512090094301 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270733310113 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨44, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (16512090094301 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270733310113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_45 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82526494258823 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270737301169 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨45, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82526494258823 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270737301169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_46 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82492561604633 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270741309693 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨46, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82492561604633 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270741309693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_47 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (3298346099189 / 4000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135372667133 / 50000000000000 : ℝ))
      (E := (cell12548 ⟨47, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (3298346099189 / 4000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (1135372667133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_48 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82424766855033 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270749314333 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨48, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82424766855033 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270749314333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_49 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82390904701639 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283844170733 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨49, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82390904701639 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283844170733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_50 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (8235706599077 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (227075736893 / 10000000000000 : ℝ))
      (E := (cell12548 ⟨50, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (8235706599077 / 10000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (227075736893 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_51 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82323250693797 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (454152264237 / 20000000000000 : ℝ))
      (E := (cell12548 ⟨51, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82323250693797 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (454152264237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_52 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41144729391117 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270765338101 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨52, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41144729391117 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270765338101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_53 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (4112784511387 / 5000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270769358009 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨53, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (4112784511387 / 5000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270769358009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_54 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82221945002113 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270773377999 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨54, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82221945002113 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270773377999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_55 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (16437644615459 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283847166983 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨55, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (16437644615459 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283847166983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_56 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (16430904885073 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283847668303 / 12500000000000 : ℝ))
      (E := (cell12548 ⟨56, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (16430904885073 / 20000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (283847668303 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_57 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (5132553063659 / 6250000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270785347077 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨57, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (5132553063659 / 6250000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270785347077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_58 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (82087196829191 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270789393233 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨58, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (82087196829191 / 100000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270789393233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12548_59 : CellCertificate 12548 (89098632445471 / 1000000000000000 : ℝ) (1673933085748161 / 1000000000000000000 : ℝ) (338225986099987 / 10000000000000000 : ℝ)
    (cell12548 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · norm_num [cell12548]
  · have h := gap_lower (n := 12548) (a := (41026783914901 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270793362651 / 100000000000000 : ℝ))
      (E := (cell12548 ⟨59, by decide⟩).energy) (xi := (338225986099987 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12548 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12548]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12548])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12548) (a := (41026783914901 / 50000000000000 : ℝ)) (b := (5130577503 / 3125000000000 : ℝ)) (q := (2270793362651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12548])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12548]

theorem cert12549_40 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (2584265896593 / 3125000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270588641577 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨40, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (2584265896593 / 3125000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270588641577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_41 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82662458257561 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (45411853133 / 2000000000000 : ℝ))
      (E := (cell12549 ⟨41, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82662458257561 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (45411853133 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_42 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (16525686300109 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227059663471 / 10000000000000 : ℝ))
      (E := (cell12549 ⟨42, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (16525686300109 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227059663471 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_43 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (2064860709753 / 2500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135300316971 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨43, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (2064860709753 / 2500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135300316971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_44 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82560448896631 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (283825581697 / 12500000000000 : ℝ))
      (E := (cell12549 ⟨44, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82560448896631 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (283825581697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_45 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (8252649299057 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141913039611 / 6250000000000 : ℝ))
      (E := (cell12549 ⟨45, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (8252649299057 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141913039611 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_46 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41246280321289 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135306345509 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨46, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41246280321289 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135306345509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_47 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20614662955861 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (113530832363 / 5000000000000 : ℝ))
      (E := (cell12549 ⟨47, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20614662955861 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (113530832363 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_48 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41212383252053 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141913792343 / 6250000000000 : ℝ))
      (E := (cell12549 ⟨48, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41212383252053 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (141913792343 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_49 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (16478180931129 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135312331017 / 50000000000000 : ℝ))
      (E := (cell12549 ⟨49, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (16478180931129 / 20000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (1135312331017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_50 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (8235706624929 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270628657733 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨50, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (8235706624929 / 10000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270628657733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_51 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82323251256411 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567658165577 / 25000000000000 : ℝ))
      (E := (cell12549 ⟨51, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82323251256411 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (567658165577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_52 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20572364912131 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227063667327 / 10000000000000 : ℝ))
      (E := (cell12549 ⟨52, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20572364912131 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (227063667327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_53 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (10281961424661 / 12500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270640687919 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨53, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (10281961424661 / 12500000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270640687919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_54 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (41110973237251 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270644703343 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨54, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (41110973237251 / 50000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270644703343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_55 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20547056213027 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270648716421 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨55, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20547056213027 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270648716421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_56 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82154526502187 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454130532943 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨56, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82154526502187 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454130532943 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_57 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (513255321231 / 625000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270656722011 / 100000000000000 : ℝ))
      (E := (cell12549 ⟨57, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (513255321231 / 625000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (2270656722011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_58 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (82087199508787 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454132141447 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨58, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (82087199508787 / 100000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454132141447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

theorem cert12549_59 : CellCertificate 12549 (890957736035947 / 10000000000000000 : ℝ) (418449912402837 / 250000000000000000 : ℝ) (169099178704139 / 5000000000000000 : ℝ)
    (cell12549 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · norm_num [cell12549]
  · have h := gap_lower (n := 12549) (a := (20513392702541 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454132935109 / 20000000000000 : ℝ))
      (E := (cell12549 ⟨59, by decide⟩).energy) (xi := (169099178704139 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12549 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12549]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12549])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12549) (a := (20513392702541 / 25000000000000 : ℝ)) (b := (164165232969 / 100000000000000 : ℝ)) (q := (454132935109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12549])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12549]

end BstLean.Part268
