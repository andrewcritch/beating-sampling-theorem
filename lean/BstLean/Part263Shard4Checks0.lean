import BstLean.Part263Shard4Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12325_0 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (84081836743389 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150276621871 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨0, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (84081836743389 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150276621871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_1 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10505842363767 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575139312821 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨1, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10505842363767 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575139312821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_2 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (84011666185187 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (230056122497 / 10000000000000 : ℝ))
      (E := (cell12325 ⟨2, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (84011666185187 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (230056122497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_3 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20994154632913 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300565232209 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨3, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20994154632913 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300565232209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_4 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83941595912841 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150284612253 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨4, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83941595912841 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150284612253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_5 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16781319658451 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287571651363 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨5, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16781319658451 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287571651363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_6 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83871625633589 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287572150023 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨6, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83871625633589 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287572150023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_7 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10479584737591 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150290600437 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨7, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10479584737591 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150290600437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_8 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83801755057747 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460117032657 / 20000000000000 : ℝ))
      (E := (cell12325 ⟨8, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83801755057747 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460117032657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_9 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (5235428566807 / 6250000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300589153341 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨9, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (5235428566807 / 6250000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300589153341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_10 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (5233248993667 / 6250000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575148294701 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨10, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (5233248993667 / 6250000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575148294701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_11 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20924283877917 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150298565561 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨11, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20924283877917 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150298565561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_12 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83662311872721 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575150283379 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨12, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83662311872721 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575150283379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_13 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (2090687823671 / 2500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150302567457 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨13, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (2090687823671 / 2500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150302567457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_14 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20898184674803 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575152285501 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨14, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20898184674803 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575152285501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_15 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83557989095211 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300613103099 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨15, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83557989095211 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300613103099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_16 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41761632050193 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575154285153 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨16, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41761632050193 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575154285153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_17 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83488563680469 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300621144217 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨17, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83488563680469 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300621144217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_18 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (83453887801369 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287578139943 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨18, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (83453887801369 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287578139943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_19 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20854809107293 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150314565097 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨19, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20854809107293 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150314565097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12326_0 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (84081820679509 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575102983499 / 25000000000000 : ℝ))
      (E := (cell12326 ⟨0, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (84081820679509 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575102983499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_1 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (84046723181481 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150207970729 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨1, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (84046723181481 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150207970729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_2 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (1050145634891 / 1250000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (287552489483 / 12500000000000 : ℝ))
      (E := (cell12326 ⟨2, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (1050145634891 / 1250000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (287552489483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_3 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83976603472019 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150211962309 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨3, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83976603472019 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150211962309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_4 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83941581187009 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (287553489903 / 12500000000000 : ℝ))
      (E := (cell12326 ⟨4, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83941581187009 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (287553489903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_5 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (335626335599 / 400000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150215954363 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨5, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (335626335599 / 400000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150215954363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_6 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (4193580578697 / 5000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (143777243869 / 6250000000000 : ℝ))
      (E := (cell12326 ⟨6, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (4193580578697 / 5000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (143777243869 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_7 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (16767332834693 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150219953641 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨7, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (16767332834693 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150219953641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_8 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (52376088539 / 62500000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150221937587 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨8, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (52376088539 / 62500000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150221937587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_9 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20941711001253 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (4600895743 / 200000000000 : ℝ))
      (E := (cell12326 ⟨9, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20941711001253 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (4600895743 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_10 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83731971165753 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300451846017 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨10, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83731971165753 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300451846017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_11 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83697123109263 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575113966047 / 25000000000000 : ℝ))
      (E := (cell12326 ⟨11, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83697123109263 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575113966047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_12 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20915574950091 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150229937609 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨12, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20915574950091 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150229937609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_13 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41813750602033 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300463827963 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨13, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41813750602033 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300463827963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_14 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83592727285559 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575116961309 / 25000000000000 : ℝ))
      (E := (cell12326 ⟨14, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83592727285559 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575116961309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_15 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (16711595602043 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300471817299 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨15, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (16711595602043 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300471817299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_16 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83523253343587 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (71889869013 / 3125000000000 : ℝ))
      (E := (cell12326 ⟨16, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83523253343587 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (71889869013 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_17 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (16697710650281 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300479824533 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨17, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (16697710650281 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300479824533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_18 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (83453877699581 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (71890119161 / 3125000000000 : ℝ))
      (E := (cell12326 ⟨18, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (83453877699581 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (71890119161 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_19 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (417096133271 / 500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (18403902703 / 800000000000 : ℝ))
      (E := (cell12326 ⟨19, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (417096133271 / 500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (18403902703 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12327_0 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (84081804618239 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575067683639 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨0, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (84081804618239 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575067683639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_1 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (84046707455393 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575068671059 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨1, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (84046707455393 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575068671059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_2 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (84011635399899 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575069679311 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨2, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (84011635399899 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575069679311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_3 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (8397658841487 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300282669761 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨3, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (8397658841487 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300282669761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_4 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41970783231809 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300286666743 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨4, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41970783231809 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300286666743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_5 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41953284754823 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460058131883 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨5, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41953284754823 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460058131883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_6 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (1677431950333 / 2000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300294656557 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨6, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (1677431950333 / 2000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300294656557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_7 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41918325224259 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575074666673 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨7, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41918325224259 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575074666673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_8 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83801728269329 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300302640129 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨8, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83801728269329 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300302640129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_9 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83766830943347 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287538330349 / 12500000000000 : ℝ))
      (E := (cell12327 ⟨9, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83766830943347 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287538330349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_10 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41865979217513 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575077656109 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨10, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41865979217513 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575077656109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_11 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (5231069419313 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300314650521 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨11, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (5231069419313 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300314650521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_12 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83662287730117 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150159306099 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨12, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83662287730117 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150159306099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_13 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83627489463361 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300322632483 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨13, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83627489463361 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300322632483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_14 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (83592715873933 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230032660193 / 10000000000000 : ℝ))
      (E := (cell12327 ⟨14, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (83592715873933 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230032660193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_15 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (16711593385441 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300330585027 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨15, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (16711593385441 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300330585027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_16 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (20880810647183 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150167293981 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨16, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (20880810647183 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150167293981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_17 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (16697708564849 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300338616677 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨17, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (16697708564849 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300338616677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_18 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (16690773519931 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150171309339 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨18, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (16690773519931 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150171309339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_19 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (1668384337621 / 2000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575086649837 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨19, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (1668384337621 / 2000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575086649837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12328_0 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (84081788559579 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150064793827 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨0, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (84081788559579 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150064793827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_1 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (84046691731873 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575033384353 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨1, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (84046691731873 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575033384353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_2 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (84011620011043 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460027514259 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨2, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (84011620011043 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460027514259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_3 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20994143340051 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575035381371 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨3, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20994143340051 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575035381371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_4 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20985387935667 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300145524933 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨4, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20985387935667 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300145524933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_5 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (4195327756097 / 5000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460029904173 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨5, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (4195327756097 / 5000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460029904173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_6 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41935791730859 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300153522059 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨6, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41935791730859 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300153522059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_7 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (654973724421 / 781250000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300157537039 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨7, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (654973724421 / 781250000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300157537039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_8 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83801714878531 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300161516113 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨8, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83801714878531 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300161516113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_9 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41883408941957 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300165525203 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨9, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41883408941957 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300165525203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_10 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83731945706491 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300169514061 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨10, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83731945706491 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300169514061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_11 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (10462137288863 / 12500000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300173490121 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨11, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (10462137288863 / 12500000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300173490121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_12 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41831137830989 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150088730283 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨12, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41831137830989 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150088730283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_13 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83627477724723 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460036298081 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨13, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83627477724723 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460036298081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_14 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83592704464333 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (230018547019 / 10000000000000 : ℝ))
      (E := (cell12328 ⟨14, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83592704464333 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (230018547019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_15 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83557955846181 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300189464409 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨15, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83557955846181 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300189464409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_16 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83523231835821 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300193479251 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨16, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83523231835821 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300193479251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_17 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83488532398987 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150098731243 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨17, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83488532398987 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150098731243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_18 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (83453857501591 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300201419741 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨18, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (83453857501591 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300201419741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_19 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41709603554861 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300205414613 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨19, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41709603554861 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300205414613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12329_0 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (42040886251763 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (574997123323 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨0, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (42040886251763 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (574997123323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_1 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (84046676010919 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (574998125247 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨1, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (84046676010919 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (574998125247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_2 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (84011604624711 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2299996478019 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨2, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (84011604624711 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2299996478019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_3 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83976558308021 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287500054243 / 12500000000000 : ℝ))
      (E := (cell12329 ⟨3, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83976558308021 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287500054243 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_4 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (524634606401 / 625000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150002217963 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨4, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (524634606401 / 625000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150002217963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_5 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41953270368317 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460001687037 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨5, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41953270368317 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460001687037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_6 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41935784704571 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300012440499 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨6, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41935784704571 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300012440499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_7 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41918311502787 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287502050307 / 12500000000000 : ℝ))
      (E := (cell12329 ⟨7, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41918311502787 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (287502050307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_8 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (10475212686251 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300020445167 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨8, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (10475212686251 / 12500000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300020445167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_9 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41883402413357 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300024402767 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨9, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41883402413357 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300024402767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_10 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83731932980147 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300028398883 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨10, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83731932980147 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300028398883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_11 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83697085914949 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230003238299 / 10000000000000 : ℝ))
      (E := (cell12329 ⟨11, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83697085914949 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230003238299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_12 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83662263595947 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300036420321 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨12, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83662263595947 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300036420321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_13 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83627465988153 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (92001616069 / 4000000000000 : ℝ))
      (E := (cell12329 ⟨13, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83627465988153 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (92001616069 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_14 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83592693056759 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460008878383 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨14, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83592693056759 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460008878383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_15 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83557944767141 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575012099331 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨15, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83557944767141 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575012099331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_16 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41761610542427 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300052365991 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨16, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41761610542427 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300052365991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_17 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (5218032623477 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150028180979 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨17, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (5218032623477 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150028180979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_18 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (83453847405389 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300060390917 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨18, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (83453847405389 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300060390917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_19 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41709598670107 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230006434189 / 10000000000000 : ℝ))
      (E := (cell12329 ⟨19, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41709598670107 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230006434189 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12330_0 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (42040878225041 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299847451471 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨0, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (42040878225041 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299847451471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_1 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (8404666029253 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114992572969 / 5000000000000 : ℝ))
      (E := (cell12330 ⟨1, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (8404666029253 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (114992572969 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_2 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (10501448655113 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149927718709 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨2, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (10501448655113 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149927718709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_3 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (1049706790729 / 1250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299859452989 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨3, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (1049706790729 / 1250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299859452989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_4 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (20985380577023 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299863457593 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨4, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (20985380577023 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299863457593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_5 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41953263176863 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299867460269 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨5, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41953263176863 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299867460269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_6 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (20967888839731 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (57496785297 / 2500000000000 : ℝ))
      (E := (cell12330 ⟨6, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (20967888839731 / 25000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (57496785297 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_7 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41918304643787 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (9199501747 / 400000000000 : ℝ))
      (E := (cell12330 ⟨7, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41918304643787 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (9199501747 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_8 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83801688103759 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149939713647 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨8, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83801688103759 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149939713647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_9 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41883395885873 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149941695727 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨9, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41883395885873 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149941695727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_10 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83731920255993 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149943697459 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨10, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83731920255993 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149943697459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_11 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (83697073521143 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (57497284679 / 2500000000000 : ℝ))
      (E := (cell12330 ⟨11, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (83697073521143 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (57497284679 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_12 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (10457781441503 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299895375361 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨12, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (10457781441503 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299895375361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_13 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (5226715890853 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299899366451 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨13, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (5226715890853 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299899366451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_14 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (8359268165121 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299903367111 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨14, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (8359268165121 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2299903367111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_15 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (16711586738017 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149953691887 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨15, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (16711586738017 / 20000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149953691887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_16 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (8352321033583 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149955682239 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨16, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (8352321033583 / 10000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149955682239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_17 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (4174425577709 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (143744710829 / 6250000000000 : ℝ))
      (E := (cell12330 ⟨17, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (4174425577709 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (143744710829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_18 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (10431729663881 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149959678817 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨18, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (10431729663881 / 12500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1149959678817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_19 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41709593786263 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (459984664593 / 20000000000000 : ℝ))
      (E := (cell12330 ⟨19, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41709593786263 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (459984664593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12331_0 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (16816348079849 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574926629991 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨0, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (16816348079849 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574926629991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_1 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (84046644576707 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299710528173 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨1, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (84046644576707 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299710528173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_2 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (84011573859619 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299714507311 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨2, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (84011573859619 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299714507311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_3 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (839765282111 / 1000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (91988740991 / 4000000000000 : ℝ))
      (E := (cell12331 ⟨3, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (839765282111 / 1000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (91988740991 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_4 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83941507594463 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299722532069 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨4, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83941507594463 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299722532069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_5 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (2622078499163 / 3125000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299726480339 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨5, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (2622078499163 / 3125000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299726480339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_6 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83871541311061 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459946098823 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨6, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83871541311061 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459946098823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_7 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83836595571889 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574933616529 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨7, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83836595571889 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574933616529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_8 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41900837359891 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (71866826953 / 3125000000000 : ℝ))
      (E := (cell12331 ⟨8, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41900837359891 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (71866826953 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_9 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83766778719009 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149871245631 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨9, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83766778719009 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149871245631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_10 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83731907534029 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299746444157 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨10, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83731907534029 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299746444157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_11 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41848530564743 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (11498752223 / 500000000000 : ℝ))
      (E := (cell12331 ⟨11, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41848530564743 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (11498752223 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_12 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83662239470209 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (229975444179 / 10000000000000 : ℝ))
      (E := (cell12331 ⟨12, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83662239470209 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (229975444179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_13 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (8362744252121 / 10000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459951688531 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨13, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (8362744252121 / 10000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459951688531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_14 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41796335123843 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149881226937 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨14, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41796335123843 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149881226937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_15 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (83557922615013 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149883211879 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨15, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (83557922615013 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149883211879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_16 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20880799897187 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299770416567 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨16, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20880799897187 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299770416567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_17 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20872125283657 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299774438239 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨17, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20872125283657 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299774438239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_18 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (10431728402321 / 12500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149889218137 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨18, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (10431728402321 / 12500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149889218137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_19 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41709588903329 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299782416053 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨19, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41709588903329 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299782416053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12332_0 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (42040862175507 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299565641003 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨0, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (42040862175507 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299565641003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_1 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (84046628863449 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299569649579 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨1, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (84046628863449 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299569649579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_2 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (42005779240429 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149786814941 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨2, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (42005779240429 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149786814941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_3 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (2099412829159 / 2500000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574894412327 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨3, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (2099412829159 / 2500000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574894412327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_4 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83941492883273 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574895414839 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨4, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83941492883273 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574895414839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_5 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (2622078049847 / 3125000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149792805587 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨5, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (2622078049847 / 3125000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149792805587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_6 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (16774305453111 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574897407323 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨6, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (16774305453111 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574897407323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_7 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41918290929259 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574898401607 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨7, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41918290929259 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574898401607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_8 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83801661338077 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299597608733 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨8, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83801661338077 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299597608733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_9 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83766765668503 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299601586231 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨9, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83766765668503 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299601586231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_10 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (16746378962851 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299605604611 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨10, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (16746378962851 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299605604611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_11 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83697048739977 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459921922669 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨11, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83697048739977 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459921922669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_12 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (167324454821 / 200000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (57490339039 / 2500000000000 : ℝ))
      (E := (cell12332 ⟨12, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (167324454821 / 200000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (57490339039 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_13 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41813715395419 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459923514453 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨13, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41813715395419 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459923514453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_14 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41796329423093 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299621594111 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨14, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41796329423093 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299621594111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_15 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (20889477885481 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574906393851 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨15, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (20889477885481 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574906393851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_16 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (83523188843609 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574907395101 / 25000000000000 : ℝ))
      (E := (cell12332 ⟨16, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (83523188843609 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (574907395101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_17 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41744245358489 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149816778441 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨17, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41744245358489 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149816778441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_18 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (20863454281987 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299637568649 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨18, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (20863454281987 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299637568649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_19 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (8341916804261 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299641562941 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨19, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (8341916804261 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299641562941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12333_0 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (84081708305389 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299424872357 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨0, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (84081708305389 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299424872357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_1 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (42023306576377 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (143714305087 / 6250000000000 : ℝ))
      (E := (cell12333 ⟨1, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (42023306576377 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (143714305087 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_2 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (42005771552309 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299432862949 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨2, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (42005771552309 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299432862949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_3 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83976498124101 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287429603323 / 12500000000000 : ℝ))
      (E := (cell12333 ⟨3, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83976498124101 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (287429603323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_4 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83941478174521 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459888167891 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨4, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83941478174521 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459888167891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_5 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83906483219387 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299444852777 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨5, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83906483219387 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299444852777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_6 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83871513222403 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149724408707 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨6, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83871513222403 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149724408707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_7 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83836568147461 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (9197811199 / 400000000000 : ℝ))
      (E := (cell12333 ⟨7, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83836568147461 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (9197811199 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_8 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (16760329591729 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459891361609 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨8, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (16760329591729 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459891361609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_9 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20941688155057 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299460792323 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨9, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20941688155057 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299460792323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_10 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (8373188209667 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (71858275571 / 3125000000000 : ℝ))
      (E := (cell12333 ⟨10, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (8373188209667 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (71858275571 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_11 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (10462129544077 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459893755467 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨11, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (10462129544077 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459893755467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_12 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41831107676449 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299472792723 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨12, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41831107676449 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299472792723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_13 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (8362741906253 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149738377641 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨13, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (8362741906253 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149738377641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_14 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (8359264744671 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149740393909 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨14, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (8359264744671 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149740393909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_15 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41778950235409 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149742390293 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨15, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41778950235409 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149742390293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_16 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83523178100411 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299488739699 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨16, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83523178100411 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299488739699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_17 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (83488480301229 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299492729193 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨17, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (83488480301229 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299492729193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_18 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20863451759797 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299496754759 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨18, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20863451759797 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299496754759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_19 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (4170957914019 / 5000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299500763629 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨19, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (4170957914019 / 5000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299500763629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12334_0 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (8408169226237 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299284156261 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨0, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (8408169226237 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299284156261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_1 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (84046597444623 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149644054013 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨1, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (84046597444623 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149644054013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_2 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (840115277309 / 1000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299292148699 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨2, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (840115277309 / 1000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299292148699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_3 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41988241542161 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (45985922289 / 2000000000000 : ℝ))
      (E := (cell12334 ⟨3, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41988241542161 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (45985922289 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_4 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83941463468207 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299300130233 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨4, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83941463468207 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299300130233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_5 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83906468846067 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574826022343 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨5, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83906468846067 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574826022343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_6 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16774299836321 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574827029099 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨6, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16774299836321 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574827029099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_7 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (20959138609679 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299312104021 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨7, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (20959138609679 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299312104021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_8 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83801634581483 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149658030219 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨8, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83801634581483 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149658030219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_9 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41883369787091 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149660025781 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨9, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41883369787091 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149660025781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_10 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (10466483672659 / 12500000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299324085147 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨10, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (10466483672659 / 12500000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299324085147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_11 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83697023967401 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287416006579 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨11, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83697023967401 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287416006579 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_12 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83662203297401 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299332077229 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨12, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83662203297401 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299332077229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_13 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83627407336287 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287417006223 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨13, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83627407336287 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287417006223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_14 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41796318024629 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299340035001 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨14, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41796318024629 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299340035001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_15 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41778944700847 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (229934403931 / 10000000000000 : ℝ))
      (E := (cell12334 ⟨15, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41778944700847 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (229934403931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_16 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16704633471831 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299348010747 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨16, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16704633471831 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299348010747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_17 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (4174423494369 / 5000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149676006673 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨17, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (4174423494369 / 5000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149676006673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_18 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41726898476143 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299355994607 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨18, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41726898476143 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299355994607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_19 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (83419148519969 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (57484000453 / 2500000000000 : ℝ))
      (E := (cell12334 ⟨19, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (83419148519969 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (57484000453 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12335_0 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16816335244391 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459828698543 / 20000000000000 : ℝ))
      (E := (cell12335 ⟨0, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16816335244391 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459828698543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_1 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16809316347811 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459829500573 / 20000000000000 : ℝ))
      (E := (cell12335 ⟨1, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16809316347811 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459829500573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_2 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (42005756179851 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574787871783 / 25000000000000 : ℝ))
      (E := (cell12335 ⟨2, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (42005756179851 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574787871783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_3 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83976468047021 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299155455067 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨3, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83976468047021 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299155455067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_4 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83941448764331 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299159473827 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨4, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83941448764331 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299159473827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_5 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41953227237571 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149581718369 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨5, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41953227237571 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149581718369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_6 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83871485143161 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149583734163 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨6, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83871485143161 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149583734163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_7 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83836540732283 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299171461307 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨7, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83836540732283 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299171461307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_8 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83801621206593 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299175423869 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨8, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83801621206593 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299175423869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_9 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41883363265183 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (229917942193 / 10000000000000 : ℝ))
      (E := (cell12335 ⟨9, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41883363265183 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (229917942193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_10 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83731856668063 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149591702617 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨10, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83731856668063 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149591702617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_11 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83697011584333 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287398422651 / 12500000000000 : ℝ))
      (E := (cell12335 ⟨11, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83697011584333 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287398422651 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_12 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83662191244009 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299191415081 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨12, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83662191244009 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299191415081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_13 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20906848903027 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (35924928089 / 1562500000000 : ℝ))
      (E := (cell12335 ⟨13, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20906848903027 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (35924928089 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_14 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20898156163457 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (14369996211 / 625000000000 : ℝ))
      (E := (cell12335 ⟨14, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20898156163457 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (14369996211 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_15 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83557878334551 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (22992034097 / 1000000000000 : ℝ))
      (E := (cell12335 ⟨15, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83557878334551 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (22992034097 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_16 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (83523156619839 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299207393549 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨16, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (83523156619839 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299207393549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_17 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (8348845947543 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149605675587 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨17, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (8348845947543 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149605675587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_18 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20863446716811 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149607673193 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨18, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20863446716811 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149607673193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_19 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (667353110091 / 800000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149609692317 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨19, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (667353110091 / 800000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149609692317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12336_0 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (16816332036829 / 20000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149501440859 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨0, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (16816332036829 / 20000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149501440859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_1 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (5252910377253 / 6250000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (143687930783 / 6250000000000 : ℝ))
      (E := (cell12336 ⟨1, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (5252910377253 / 6250000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (143687930783 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_2 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (3360459879641 / 4000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287376359781 / 12500000000000 : ℝ))
      (E := (cell12336 ⟨2, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (3360459879641 / 4000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287376359781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_3 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83976453012199 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299014848433 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨3, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83976453012199 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299014848433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_4 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83941434062891 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149509435119 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨4, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83941434062891 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149509435119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_5 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83906440106613 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149511418493 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨5, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83906440106613 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149511418493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_6 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83871471107071 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459805374641 / 20000000000000 : ℝ))
      (E := (cell12336 ⟨6, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83871471107071 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459805374641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_7 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83836527028161 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299030871609 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨7, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83836527028161 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299030871609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_8 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (20950401958493 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (35922419381 / 1562500000000 : ℝ))
      (E := (cell12336 ⟨8, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (20950401958493 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (35922419381 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_9 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41883356744389 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149519422723 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨9, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41883356744389 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149519422723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_10 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83731843957041 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299042836541 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨10, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83731843957041 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299042836541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_11 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83696999203411 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299046821093 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨11, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83696999203411 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299046821093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_12 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41831089596361 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299050806279 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨12, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41831089596361 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299050806279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_13 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (10453422986249 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299054799021 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨13, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (10453422986249 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299054799021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_14 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83592613260421 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574764701499 / 25000000000000 : ℝ))
      (E := (cell12336 ⟨14, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83592613260421 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574764701499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_15 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (8355786726939 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299062775509 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨15, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (8355786726939 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299062775509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_16 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (83523145882463 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299066771813 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨16, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (83523145882463 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299066771813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_17 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (4174422453269 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459814160169 / 20000000000000 : ℝ))
      (E := (cell12336 ⟨17, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (4174422453269 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459814160169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_18 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (4172688839203 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (22990748101 / 1000000000000 : ℝ))
      (E := (cell12336 ⟨18, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (4172688839203 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (22990748101 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_19 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (417095645023 / 500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299078804951 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨19, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (417095645023 / 500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299078804951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12337_0 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (84081644148937 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298862381047 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨0, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (84081644148937 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298862381047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_1 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (84046550335603 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574716598151 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨1, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (84046550335603 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574716598151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_2 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (84011481624867 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298870379869 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨2, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (84011481624867 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298870379869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_3 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (16795287595971 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298874352393 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨3, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (16795287595971 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298874352393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_4 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83941419363887 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574719594333 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨4, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83941419363887 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574719594333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_5 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83906425740477 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298882348009 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨5, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83906425740477 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298882348009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_6 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83871457073333 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459777266207 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨6, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83871457073333 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459777266207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_7 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83836513326351 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298890334927 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨7, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83836513326351 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298890334927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_8 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83801594463621 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (114944715499 / 5000000000000 : ℝ))
      (E := (cell12337 ⟨8, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83801594463621 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (114944715499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_9 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41883350224709 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298898322111 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨9, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41883350224709 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298898322111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_10 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (16746366249641 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298902321063 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨10, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (16746366249641 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298902321063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_11 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41848493412317 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (114945315713 / 5000000000000 : ℝ))
      (E := (cell12337 ⟨11, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41848493412317 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (114945315713 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_12 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83662167143539 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574727577219 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨12, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83662167143539 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574727577219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_13 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83627372169939 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459782862367 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨13, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83627372169939 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459782862367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_14 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (16718520373807 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298918271711 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨14, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (16718520373807 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298918271711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_15 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (8355785620621 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574730577777 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨15, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (8355785620621 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574730577777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_16 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83523135147027 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149463130917 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨16, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83523135147027 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149463130917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_17 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (20872109664307 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149465123011 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨17, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (20872109664307 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149465123011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_18 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41726883351367 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298934269359 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨18, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41726883351367 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2298934269359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_19 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (83419119249641 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (91957531163 / 4000000000000 : ℝ))
      (E := (cell12337 ⟨19, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (83419119249641 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (91957531163 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12338_0 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (84081628116333 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (229872193293 / 10000000000000 : ℝ))
      (E := (cell12338 ⟨0, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (84081628116333 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (229872193293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_1 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (84046534637719 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298725945301 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨1, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (84046534637719 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298725945301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_2 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (21002866565307 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298729934177 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨2, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (21002866565307 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298729934177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_3 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83976422949987 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574683477277 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨3, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83976422949987 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574683477277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_4 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41970702333659 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149368939691 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨4, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41970702333659 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149368939691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_5 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16781282275347 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149370955959 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨5, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16781282275347 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149370955959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_6 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83871443041947 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298745899731 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨6, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83871443041947 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298745899731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_7 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20959124906713 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (5746874773 / 250000000000 : ℝ))
      (E := (cell12338 ⟨7, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20959124906713 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (5746874773 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_8 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83801581095539 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149376945311 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨8, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83801581095539 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149376945311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_9 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16753337482457 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298757851929 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨9, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16753337482457 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298757851929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_10 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20932954635389 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298761858803 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨10, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20932954635389 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298761858803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_11 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41848487224001 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298765860709 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨11, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41848487224001 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298765860709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_12 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (4183107754823 / 5000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149384932411 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨12, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (4183107754823 / 5000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149384932411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_13 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20906840112987 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (143673367379 / 6250000000000 : ℝ))
      (E := (cell12338 ⟨13, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20906840112987 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (143673367379 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_14 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (8359259047967 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298777849007 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨14, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (8359259047967 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298777849007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_15 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (83557845145009 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574695460533 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨15, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (83557845145009 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574695460533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_16 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (8352312441353 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298785805467 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨16, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (8352312441353 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298785805467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_17 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41744214125487 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298789803047 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨17, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41744214125487 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298789803047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_18 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16690751324653 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298793840557 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨18, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16690751324653 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298793840557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_19 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41709554748249 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (71837431469 / 3125000000000 : ℝ))
      (E := (cell12338 ⟨19, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41709554748249 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (71837431469 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12339_0 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (84081612086331 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298581537369 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨0, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (84081612086331 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298581537369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_1 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (16809303788479 / 20000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149292775311 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨1, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (16809303788479 / 20000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149292775311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_2 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (21002862725027 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (91943581647 / 4000000000000 : ℝ))
      (E := (cell12339 ⟨2, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (21002862725027 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (91943581647 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_3 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20994101980649 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298593518579 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨3, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20994101980649 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298593518579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_4 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (1311584218331 / 1562500000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459719509997 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨4, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (1311584218331 / 1562500000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459719509997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_5 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41953198507693 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574650382179 / 25000000000000 : ℝ))
      (E := (cell12339 ⟨5, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41953198507693 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574650382179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_6 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (5241964313307 / 6250000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149302760691 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨6, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (5241964313307 / 6250000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149302760691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_7 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41918242964831 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459721907299 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨7, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41918242964831 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459721907299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_8 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (3352062709189 / 4000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298613524351 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨8, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (3352062709189 / 4000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298613524351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_9 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (4188333718869 / 5000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298617492881 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨9, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (4188333718869 / 5000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298617492881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_10 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20932951459273 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287327688471 / 12500000000000 : ℝ))
      (E := (cell12339 ⟨10, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20932951459273 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287327688471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_11 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41848481036757 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574656365111 / 25000000000000 : ℝ))
      (E := (cell12339 ⟨11, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41848481036757 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574656365111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_12 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83662143051483 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (57465736853 / 2500000000000 : ℝ))
      (E := (cell12339 ⟨12, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83662143051483 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (57465736853 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_13 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83627348736019 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298633497709 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨13, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83627348736019 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298633497709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_14 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41796289546163 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149318739893 / 50000000000000 : ℝ))
      (E := (cell12339 ⟨14, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41796289546163 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (1149318739893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_15 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83557834085789 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (91945659393 / 4000000000000 : ℝ))
      (E := (cell12339 ⟨15, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83557834085789 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (91945659393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_16 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83523113681971 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (114932273043 / 5000000000000 : ℝ))
      (E := (cell12339 ⟨16, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83523113681971 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (114932273043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_17 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (83488417846619 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (28733118399 / 1250000000000 : ℝ))
      (E := (cell12339 ⟨17, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (83488417846619 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (28733118399 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_18 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20863436636413 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298653465499 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨18, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20863436636413 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298653465499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_19 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20854774936293 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287332180871 / 12500000000000 : ℝ))
      (E := (cell12339 ⟨19, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20854774936293 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287332180871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12340_0 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (8408159605893 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298441252139 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨0, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (8408159605893 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298441252139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_1 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (84046503249631 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149222633181 / 50000000000000 : ℝ))
      (E := (cell12340 ⟨1, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (84046503249631 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149222633181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_2 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (16802287108301 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298449258683 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨2, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (16802287108301 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298449258683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_3 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83976392897681 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298453238649 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨3, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83976392897681 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298453238649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_4 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20985343820371 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298457215547 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨4, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20985343820371 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298457215547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_5 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (8390638265643 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574615299601 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨5, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (8390638265643 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574615299601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_6 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20967853746557 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (229846519599 / 10000000000000 : ℝ))
      (E := (cell12340 ⟨6, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20967853746557 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (229846519599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_7 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83836472234781 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298469216813 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨7, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83836472234781 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298469216813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_8 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83801554366179 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298473211169 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨8, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83801554366179 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298473211169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_9 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83766661344701 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574619296747 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨9, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83766661344701 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574619296747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_10 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83731793134813 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298481209953 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨10, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83731793134813 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298481209953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_11 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (8369694970117 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (459697034299 / 20000000000000 : ℝ))
      (E := (cell12340 ⟨11, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (8369694970117 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (459697034299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_12 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83662131008609 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298489194823 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨12, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83662131008609 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298489194823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_13 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (10453417127769 / 12500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574623292693 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨13, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (10453417127769 / 12500000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574623292693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_14 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83592567707003 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298497164047 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨14, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83592567707003 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298497164047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_15 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83557823028547 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (229850118107 / 10000000000000 : ℝ))
      (E := (cell12340 ⟨15, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83557823028547 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (229850118107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_16 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83523102952351 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298505169869 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨16, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83523102952351 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298505169869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_17 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (260901273263 / 312500000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (459701827261 / 20000000000000 : ℝ))
      (E := (cell12340 ⟨17, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (260901273263 / 312500000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (459701827261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_18 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83453736469897 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298513144187 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨18, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83453736469897 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298513144187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_19 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (83419089995661 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298517140739 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨19, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (83419089995661 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298517140739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12341_0 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (8408158003413 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574575254867 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨0, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (8408158003413 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574575254867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_1 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (3361859502377 / 4000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298305034729 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨1, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (3361859502377 / 4000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298305034729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_2 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (84011420185419 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287288621383 / 12500000000000 : ℝ))
      (E := (cell12341 ⟨2, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (84011420185419 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (287288621383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_3 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41988188937621 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298313011477 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨3, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41988188937621 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298313011477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_4 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41970680296109 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298316991799 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨4, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41970680296109 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298316991799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_5 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16781273659973 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298320978873 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨5, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16781273659973 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298320978873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_6 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16774280192379 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149162490733 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨6, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16774280192379 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149162490733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_7 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83836458542209 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149164475077 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨7, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83836458542209 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149164475077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_8 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (838015410049 / 1000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298332951077 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨8, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (838015410049 / 1000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298332951077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_9 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83766648314247 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574584233563 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨9, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83766648314247 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574584233563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_10 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83731780434719 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28729262067 / 1250000000000 : ℝ))
      (E := (cell12341 ⟨10, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83731780434719 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28729262067 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_11 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (8369693733097 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298344935833 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨11, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (8369693733097 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298344935833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_12 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83662118967837 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (91933956433 / 4000000000000 : ℝ))
      (E := (cell12341 ⟨12, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83662118967837 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (91933956433 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_13 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16725465062069 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574588238833 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨13, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16725465062069 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574588238833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_14 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83592556323699 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298356901793 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨14, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83592556323699 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298356901793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_15 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (20889452993321 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (143647558179 / 6250000000000 : ℝ))
      (E := (cell12341 ⟨15, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (20889452993321 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (143647558179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_16 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83523092224669 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298364932493 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨16, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83523092224669 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298364932493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_17 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41744198521799 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298368912541 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨17, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41744198521799 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298368912541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_18 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (83453726395997 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149186438311 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨18, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (83453726395997 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149186438311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_19 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16683816049593 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298376888323 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨19, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16683816049593 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298376888323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12342_0 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (8408156401193 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298160839359 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨0, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (8408156401193 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298160839359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_1 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (42023235935889 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298164855723 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨1, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (42023235935889 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298164855723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_2 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (1680228096637 / 2000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298168851777 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨2, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (1680228096637 / 2000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298168851777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_3 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83976362855277 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298172837067 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨3, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83976362855277 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298172837067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_4 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (10492668238173 / 12500000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149088410439 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨4, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (10492668238173 / 12500000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149088410439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_5 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20976588486423 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149090406117 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨5, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20976588486423 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149090406117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_6 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83871386939911 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298184819903 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨6, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83871386939911 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298184819903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_7 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41918222425973 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287273599307 / 12500000000000 : ℝ))
      (E := (cell12342 ⟨7, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41918222425973 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287273599307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_8 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (1309398869467 / 1562500000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459638560407 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨8, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (1309398869467 / 1562500000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459638560407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_9 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83766635286019 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (143637299541 / 6250000000000 : ℝ))
      (E := (cell12342 ⟨9, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83766635286019 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (143637299541 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_10 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83731767736809 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298200773991 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨10, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83731767736809 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298200773991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_11 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83696924962911 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149102376731 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨11, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83696924962911 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149102376731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_12 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83662106929167 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298208738237 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨12, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83662106929167 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298208738237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_13 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83627313600599 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574553183809 / 25000000000000 : ℝ))
      (E := (cell12342 ⟨13, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83627313600599 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574553183809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_14 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41796272471207 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287277093891 / 12500000000000 : ℝ))
      (E := (cell12342 ⟨14, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41796272471207 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287277093891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_15 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83557800919999 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298220734211 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨15, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83557800919999 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298220734211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_16 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83523081498923 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (35909761699 / 1562500000000 : ℝ))
      (E := (cell12342 ⟨16, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83523081498923 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (35909761699 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_17 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (83488386644933 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298228742461 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨17, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (83488386644933 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298228742461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_18 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (5215857270247 / 6250000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298232721 / 100000000000 : ℝ))
      (E := (cell12342 ⟨18, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (5215857270247 / 6250000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298232721 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_19 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20854767625521 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298236747939 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨19, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20854767625521 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298236747939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12343_0 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8408154799233 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (143626298099 / 6250000000000 : ℝ))
      (E := (cell12343 ⟨0, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8408154799233 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (143626298099 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_1 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (84046456186689 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149012364673 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨1, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (84046456186689 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149012364673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_2 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (84011389480797 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298028727367 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨2, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (84011389480797 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298028727367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_3 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41988173918893 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114901635771 / 5000000000000 : ℝ))
      (E := (cell12343 ⟨3, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41988173918893 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114901635771 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_4 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83941331220983 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298036702787 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨4, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83941331220983 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298036702787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_5 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83906339593909 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574510174623 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨5, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83906339593909 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574510174623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_6 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83871372920277 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298044711301 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨6, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83871372920277 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298044711301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_7 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8383643116399 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149024345893 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨7, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8383643116399 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149024345893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_8 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41900757144571 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287256588261 / 12500000000000 : ℝ))
      (E := (cell12343 ⟨8, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41900757144571 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287256588261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_9 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (5235413891251 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114902835211 / 5000000000000 : ℝ))
      (E := (cell12343 ⟨9, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (5235413891251 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114902835211 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_10 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41865877520541 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149030346927 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨10, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41865877520541 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149030346927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_11 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (16739382519399 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574516170603 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨11, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (16739382519399 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574516170603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_12 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83662094892597 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114903433853 / 5000000000000 : ℝ))
      (E := (cell12343 ⟨12, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83662094892597 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114903433853 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_13 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (5226706368307 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298072684717 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨13, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (5226706368307 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298072684717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_14 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20898133390787 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (45961533079 / 2000000000000 : ℝ))
      (E := (cell12343 ⟨14, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20898133390787 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (45961533079 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_15 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20889447467173 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574520162309 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨15, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20889447467173 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574520162309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_16 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (16704614155023 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149042309299 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨16, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (16704614155023 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149042309299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_17 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83488376248163 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149044313033 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨17, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83488376248163 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149044313033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_18 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83453706253763 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287261577391 / 12500000000000 : ℝ))
      (E := (cell12343 ⟨18, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83453706253763 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287261577391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_19 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (83419060758017 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298096603153 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨19, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (83419060758017 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298096603153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12344_0 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (84081531975329 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148940347301 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨0, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (84081531975329 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148940347301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_1 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (21011610126039 / 25000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148942356699 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨1, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (21011610126039 / 25000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148942356699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_2 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (84011374132259 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148944356737 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨2, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (84011374132259 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148944356737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_3 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (5248520801423 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297892704379 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨3, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (5248520801423 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297892704379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_4 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41970658269507 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297896695391 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨4, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41970658269507 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297896695391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_5 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83906325244517 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148950347767 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨5, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83906325244517 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148950347767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_6 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83871358902991 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297904655661 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨6, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83871358902991 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297904655661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_7 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83836417478341 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (71809645067 / 3125000000000 : ℝ))
      (E := (cell12344 ⟨7, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83836417478341 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (71809645067 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_8 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41900750467331 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148956331617 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨8, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41900750467331 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148956331617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_9 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83766609236237 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (143619791809 / 6250000000000 : ℝ))
      (E := (cell12344 ⟨9, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83766609236237 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (143619791809 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_10 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41865871173769 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (35905010421 / 1562500000000 : ℝ))
      (E := (cell12344 ⟨10, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41865871173769 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (35905010421 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_11 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83696900233221 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297924664653 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨11, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83696900233221 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297924664653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_12 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (5228880178633 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148964305593 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨12, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (5228880178633 / 6250000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148964305593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_13 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (16725458037457 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287241578693 / 12500000000000 : ℝ))
      (E := (cell12344 ⟨13, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (16725458037457 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287241578693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_14 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (835925221859 / 1000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148968305131 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨14, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (835925221859 / 1000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1148968305131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_15 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41778889409681 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287242577227 / 12500000000000 : ℝ))
      (E := (cell12344 ⟨15, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41778889409681 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (287242577227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_16 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41761530026621 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297944600229 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨16, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41761530026621 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297944600229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_17 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (10436045731661 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297948621529 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨17, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (10436045731661 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297948621529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_18 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83453696185427 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574488157301 / 25000000000000 : ℝ))
      (E := (cell12344 ⟨18, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83453696185427 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574488157301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_19 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (83419051015763 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297956570403 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨19, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (83419051015763 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2297956570403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12345_0 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (42040757980463 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148870364979 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨0, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (42040757980463 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148870364979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_1 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (4202321241209 / 5000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (897556543 / 39062500000 : ℝ))
      (E := (cell12345 ⟨1, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (4202321241209 / 5000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (897556543 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_2 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16802271757247 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (57443718807 / 2500000000000 : ℝ))
      (E := (cell12345 ⟨2, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16802271757247 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (57443718807 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_3 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (5248519863139 / 6250000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148876373051 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨3, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (5248519863139 / 6250000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148876373051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_4 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20985325464869 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148878370413 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨4, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20985325464869 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148878370413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_5 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41953155448757 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (91910429819 / 4000000000000 : ℝ))
      (E := (cell12345 ⟨5, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41953155448757 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (91910429819 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_6 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83871344888053 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148882355449 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨6, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83871344888053 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148882355449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_7 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41918201897499 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297768703469 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨7, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41918201897499 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297768703469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_8 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41900743791223 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297772673477 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨8, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41900743791223 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297772673477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_9 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41883298107341 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297776686829 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨9, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41883298107341 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297776686829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_10 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (5233233103511 / 6250000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297780693261 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨10, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (5233233103511 / 6250000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297780693261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_11 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83696887871587 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297784700189 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨11, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83696887871587 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297784700189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_12 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41831035412879 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297788656727 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨12, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41831035412879 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297788656727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_13 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20906819620929 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148896342937 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨13, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20906819620929 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148896342937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_14 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83592510810669 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148898339083 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨14, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83592510810669 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148898339083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_15 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83557767772009 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (143612539997 / 6250000000000 : ℝ))
      (E := (cell12345 ⟨15, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83557767772009 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (143612539997 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_16 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16704609866661 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148902317741 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨16, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16704609866661 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148902317741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_17 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83488355460309 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297808670679 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨17, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83488355460309 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297808670679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_18 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41726843059473 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297812634837 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨18, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41726843059473 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297812634837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_19 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (83419041275323 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287227081211 / 12500000000000 : ℝ))
      (E := (cell12345 ⟨19, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (83419041275323 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287227081211 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12346_0 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (84081499949121 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148800437827 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨0, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (84081499949121 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148800437827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_1 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (2101160228669 / 2500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148802419699 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨1, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (2101160228669 / 2500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148802419699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_2 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (42005671721363 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297608843787 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨2, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (42005671721363 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297608843787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_3 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (10497037850019 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (143600802537 / 6250000000000 : ℝ))
      (E := (cell12346 ⟨3, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (10497037850019 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (143600802537 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_4 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83941287182369 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459523367819 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨4, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83941287182369 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459523367819 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_5 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (839062965529 / 1000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459524169663 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨5, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (839062965529 / 1000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459524169663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_6 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41935665437731 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148812409551 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨6, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41935665437731 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148812409551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_7 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41918195056981 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148814408913 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨7, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41918195056981 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148814408913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_8 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (5237592139531 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297632794777 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨8, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (5237592139531 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297632794777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_9 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83766583195349 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287204601983 / 12500000000000 : ℝ))
      (E := (cell12346 ⟨9, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83766583195349 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287204601983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_10 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20932929241749 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287205096601 / 12500000000000 : ℝ))
      (E := (cell12346 ⟨10, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20932929241749 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287205096601 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_11 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41848437756047 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297644789021 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨11, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41848437756047 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297644789021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_12 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (2614439337359 / 3125000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297648755629 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨12, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (2614439337359 / 3125000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297648755629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_13 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41813633391103 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297652795631 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨13, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41813633391103 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297652795631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_14 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (5224531214841 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297656799563 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨14, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (5224531214841 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297656799563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_15 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (10444719590829 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574415193443 / 25000000000000 : ℝ))
      (E := (cell12346 ⟨15, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (10444719590829 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574415193443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_16 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (10440379826913 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148832391253 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨16, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (10440379826913 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148832391253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_17 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83488345069223 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297668773519 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨17, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83488345069223 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297668773519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_18 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (83453676054319 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (114883637621 / 5000000000000 : ℝ))
      (E := (cell12346 ⟨18, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (83453676054319 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (114883637621 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_19 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (10427378942087 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (91907068983 / 4000000000000 : ℝ))
      (E := (cell12346 ⟨19, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (10427378942087 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (91907068983 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12347_0 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (84081483939913 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297461016147 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨0, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (84081483939913 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297461016147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_1 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (10505799183987 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459493007829 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨1, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (10505799183987 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459493007829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_2 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (84011328101729 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459493809163 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨2, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (84011328101729 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459493809163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_3 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83976287792551 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297472987851 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨3, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83976287792551 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297472987851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_4 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83941272507691 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148738495099 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨4, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83941272507691 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148738495099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_5 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (3356251288427 / 4000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459496200811 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨5, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (3356251288427 / 4000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459496200811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_6 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (41935658432609 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297484980271 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨6, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (41935658432609 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297484980271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_7 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (8383637643523 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (17949132697 / 781250000000 : ℝ))
      (E := (cell12347 ⟨7, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (8383637643523 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (17949132697 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_8 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83801460884809 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297492969177 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨8, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83801460884809 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297492969177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_9 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (261770531807 / 312500000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297496998061 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨9, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (261770531807 / 312500000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297496998061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_10 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83731704279997 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297500963593 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨10, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83731704279997 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297500963593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_11 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83696863154741 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114875249459 / 5000000000000 : ℝ))
      (E := (cell12347 ⟨11, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83696863154741 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (114875249459 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_12 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83662046767317 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148754482973 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨12, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83662046767317 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148754482973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_13 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83627255082753 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71797279963 / 3125000000000 : ℝ))
      (E := (cell12347 ⟨13, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83627255082753 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (71797279963 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_14 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (4179624403313 / 5000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297516974453 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨14, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (4179624403313 / 5000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297516974453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_15 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (8355774568323 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297520961151 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨15, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (8355774568323 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297520961151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_16 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83523027899237 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297524925007 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨16, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83523027899237 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297524925007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_17 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (83488334680031 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297528930049 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨17, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (83488334680031 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297528930049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_18 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (10431708248943 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297532923759 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨18, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (10431708248943 / 12500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297532923759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_19 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (2085475544997 / 2500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297536911503 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨19, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (2085475544997 / 2500000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297536911503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12348_0 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (42040733966651 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297321266983 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨0, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (42040733966651 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297321266983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_1 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (16809275559917 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297325291533 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨1, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (16809275559917 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297325291533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_2 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (42005656381623 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297329242727 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨2, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (42005656381623 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297329242727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_3 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83976272787421 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574333311431 / 25000000000000 : ℝ))
      (E := (cell12348 ⟨3, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83976272787421 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574333311431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_4 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83941257835443 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459467450401 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨4, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83941257835443 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459467450401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_5 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83906267870837 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297341270589 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨5, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83906267870837 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297341270589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_6 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83871302857321 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297345252323 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨6, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83871302857321 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297345252323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_7 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (20959090689701 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297349205641 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨7, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (20959090689701 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297349205641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_8 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (16760289507877 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297353254639 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨8, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (16760289507877 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297353254639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_9 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (10470819645419 / 12500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297357233427 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨9, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (10470819645419 / 12500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297357233427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_10 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83731691595179 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297361207611 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨10, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83731691595179 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297361207611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_11 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (10462106349941 / 12500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148682592303 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨11, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (10462106349941 / 12500000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148682592303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_12 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (20915508685311 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297369229629 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨12, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (20915508685311 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297369229629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_13 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83627243385357 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287171646929 / 12500000000000 : ℝ))
      (E := (cell12348 ⟨13, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83627243385357 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287171646929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_14 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83592476697079 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (57434430071 / 2500000000000 : ℝ))
      (E := (cell12348 ⟨14, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83592476697079 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (57434430071 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_15 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83557734641803 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297381202091 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨15, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83557734641803 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297381202091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_16 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (5220188574069 / 6250000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574346294821 / 25000000000000 : ℝ))
      (E := (cell12348 ⟨16, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (5220188574069 / 6250000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574346294821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_17 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83488324292733 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297389198443 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨17, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83488324292733 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297389198443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_18 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41726827965311 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459478629771 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨18, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41726827965311 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459478629771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_19 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (83419012064877 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297397152253 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨19, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (83419012064877 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297397152253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12349_0 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (42040725964643 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287147696299 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨0, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (42040725964643 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287147696299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_1 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (84046362129829 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148592798279 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨1, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (84046362129829 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148592798279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_2 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (3360451897091 / 4000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459437910033 / 20000000000000 : ℝ))
      (E := (cell12349 ⟨2, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (3360451897091 / 4000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459437910033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_3 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41988128892381 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (143574597273 / 6250000000000 : ℝ))
      (E := (cell12349 ⟨3, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41988128892381 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (143574597273 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_4 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (10492655395703 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297197566649 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨4, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (10492655395703 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297197566649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_5 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41953126766693 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297201532137 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨5, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41953126766693 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297201532137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_6 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83871288851769 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148602788673 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨6, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83871288851769 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148602788673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_7 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83836349084681 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (28715119213 / 1250000000000 : ℝ))
      (E := (cell12349 ⟨7, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83836349084681 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (28715119213 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_8 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (327349352329 / 390625000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148606767621 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨8, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (327349352329 / 390625000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148606767621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_9 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (16753308830137 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297217521961 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨9, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (16753308830137 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297217521961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_10 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83731678912541 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (71788172027 / 3125000000000 : ℝ))
      (E := (cell12349 ⟨10, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83731678912541 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (71788172027 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_11 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83696838446453 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574306372841 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨11, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83696838446453 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574306372841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_12 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (83662022717269 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297229488623 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨12, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (83662022717269 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297229488623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_13 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41813615845009 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574308375889 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨13, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41813615845009 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574308375889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_14 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41796232664957 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297237484723 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨14, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41796232664957 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297237484723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_15 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (5222357725147 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148620748297 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨15, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (5222357725147 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148620748297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_16 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (16704601294581 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574311371797 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨16, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (16704601294581 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574311371797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_17 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (652252452401 / 781250000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148624731179 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨17, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (652252452401 / 781250000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148624731179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_18 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (1303963216743 / 1562500000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459450697181 / 20000000000000 : ℝ))
      (E := (cell12349 ⟨18, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (1303963216743 / 1562500000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459450697181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_19 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (16683800466337 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297257446827 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨19, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (16683800466337 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297257446827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

end BstLean.Part263
