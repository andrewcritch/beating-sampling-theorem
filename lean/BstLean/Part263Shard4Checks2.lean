import BstLean.Part263Shard4Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12325_40 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82697160466907 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287589127751 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨40, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82697160466907 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287589127751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_41 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82663040010583 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300716999899 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨41, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82663040010583 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300716999899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_42 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16525788665499 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150360506749 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨42, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16525788665499 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150360506749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_43 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82594870387659 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (143795312741 / 6250000000000 : ℝ))
      (E := (cell12325 ⟨43, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82594870387659 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (143795312741 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_44 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20640205290311 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575182257329 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨44, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20640205290311 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575182257329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_45 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10315849452321 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300732971617 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨45, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10315849452321 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300732971617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_46 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82492793730099 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287592125793 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨46, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82492793730099 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287592125793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_47 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10307351933307 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150370507387 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨47, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10307351933307 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150370507387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_48 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (20606215199601 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287593124447 / 12500000000000 : ℝ))
      (E := (cell12325 ⟨48, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (20606215199601 / 25000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (287593124447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_49 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10298866212107 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150374503063 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨49, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10298866212107 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150374503063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_50 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82357022132871 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300752985787 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨50, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82357022132871 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300752985787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_51 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41161569038827 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300756991551 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨51, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41161569038827 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300756991551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_52 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16457855500511 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575190240577 / 25000000000000 : ℝ))
      (E := (cell12325 ⟨52, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16457855500511 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (575190240577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_53 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (41127720189533 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (143797809667 / 6250000000000 : ℝ))
      (E := (cell12325 ⟨53, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (41127720189533 / 50000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (143797809667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_54 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10277703334853 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (23007689661 / 1000000000000 : ℝ))
      (E := (cell12325 ⟨54, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10277703334853 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (23007689661 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_55 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (82187836373607 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150386496919 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨55, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (82187836373607 / 100000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150386496919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_56 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (10269258679417 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150388487917 / 50000000000000 : ℝ))
      (E := (cell12325 ⟨56, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (10269258679417 / 12500000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (1150388487917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_57 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (8212032583607 / 10000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460156193591 / 20000000000000 : ℝ))
      (E := (cell12325 ⟨57, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (8212032583607 / 10000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (460156193591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_58 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (8208660554801 / 10000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300784966817 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨58, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (8208660554801 / 10000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300784966817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12325_59 : CellCertificate 12325 (224368234898463 / 2500000000000000 : ℝ) (1704230330826423 / 1000000000000000000 : ℝ) (34450427806201 / 1000000000000000 : ℝ)
    (cell12325 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · norm_num [cell12325]
  · have h := gap_lower (n := 12325) (a := (16410581708699 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300788968829 / 100000000000000 : ℝ))
      (E := (cell12325 ⟨59, by decide⟩).energy) (xi := (34450427806201 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12325 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12325]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12325])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12325) (a := (16410581708699 / 20000000000000 : ℝ)) (b := (16718751617 / 10000000000000 : ℝ)) (q := (2300788968829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12325])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12325]

theorem cert12326_40 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (3307886298029 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (143785733397 / 6250000000000 : ℝ))
      (E := (cell12326 ⟨40, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (3307886298029 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (143785733397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_41 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82663037311351 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300575743087 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨41, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82663037311351 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300575743087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_42 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (3305157637791 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460115945907 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨42, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (3305157637791 / 4000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460115945907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_43 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82594868321013 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460116738691 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨43, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82594868321013 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460116738691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_44 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (16512163882047 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300587693191 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨44, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (16512163882047 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300587693191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_45 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82526794182759 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460118345627 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨45, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82526794182759 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460118345627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_46 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (16498558521811 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300595679757 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨46, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (16498558521811 / 20000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300595679757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_47 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41229407329871 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460119944699 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨47, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41229407329871 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460119944699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_48 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41212430152793 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460120736293 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨48, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41212430152793 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460120736293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_49 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82390929517501 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230060766989 / 10000000000000 : ℝ))
      (E := (cell12326 ⟨49, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82390929517501 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (230060766989 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_50 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (41178511133273 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300611687081 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨50, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (41178511133273 / 50000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300611687081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_51 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (10290392315491 / 12500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150307836081 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨51, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (10290392315491 / 12500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150307836081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_52 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20572319565249 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460123936387 / 20000000000000 : ℝ))
      (E := (cell12326 ⟨52, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20572319565249 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (460123936387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_53 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (20563860362311 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575155928517 / 25000000000000 : ℝ))
      (E := (cell12326 ⟨53, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (20563860362311 / 25000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575155928517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_54 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (8222162806031 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300627706979 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨54, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (8222162806031 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300627706979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_55 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82187838065973 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (28757895723 / 1250000000000 : ℝ))
      (E := (cell12326 ⟨55, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82187838065973 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (28757895723 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_56 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (10269258929769 / 12500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2246714533 / 97656250000 : ℝ))
      (E := (cell12326 ⟨56, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (10269258929769 / 12500000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2246714533 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_57 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (8212032814891 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575159914377 / 25000000000000 : ℝ))
      (E := (cell12326 ⟨57, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (8212032814891 / 10000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (575159914377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_58 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82086608170447 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150321849901 / 50000000000000 : ℝ))
      (E := (cell12326 ⟨58, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82086608170447 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (1150321849901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12326_59 : CellCertificate 12326 (897443347522883 / 10000000000000000 : ℝ) (1704092020939661 / 1000000000000000000 : ℝ) (344475592907579 / 10000000000000000 : ℝ)
    (cell12326 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · norm_num [cell12326]
  · have h := gap_lower (n := 12326) (a := (82052911475103 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300647686839 / 100000000000000 : ℝ))
      (E := (cell12326 ⟨59, by decide⟩).energy) (xi := (344475592907579 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12326 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12326]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12326])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12326) (a := (82052911475103 / 100000000000000 : ℝ)) (b := (167173773829 / 100000000000000 : ℝ)) (q := (2300647686839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12326])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12326]

theorem cert12327_40 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82697154435519 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (46008610037 / 2000000000000 : ℝ))
      (E := (cell12327 ⟨40, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82697154435519 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (46008610037 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_41 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82663034613057 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300434482759 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨41, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82663034613057 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300434482759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_42 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82628938562953 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300438500853 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨42, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82628938562953 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300438500853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_43 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (3303794650209 / 4000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (115022124859 / 5000000000000 : ℝ))
      (E := (cell12327 ⟨43, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (3303794650209 / 4000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (115022124859 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_44 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (20640204415011 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (28755580891 / 1250000000000 : ℝ))
      (E := (cell12327 ⟨44, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (20640204415011 / 25000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (28755580891 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_45 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82526792747729 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300450481299 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨45, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82526792747729 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300450481299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_46 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82492791488751 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150227233779 / 50000000000000 : ℝ))
      (E := (cell12327 ⟨46, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82492791488751 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (1150227233779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_47 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82458813853729 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300458487817 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨47, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82458813853729 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300458487817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_48 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (8242485981343 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460092496383 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨48, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (8242485981343 / 10000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460092496383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_49 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (5149433083673 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460093289661 / 20000000000000 : ℝ))
      (E := (cell12327 ⟨49, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (5149433083673 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (460093289661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_50 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (16471404480161 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300470444167 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨50, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (16471404480161 / 20000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300470444167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_51 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41161569485373 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575118616899 / 25000000000000 : ℝ))
      (E := (cell12327 ⟨51, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41161569485373 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (575118616899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_52 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41144639509971 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (57511961437 / 2500000000000 : ℝ))
      (E := (cell12327 ⟨52, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41144639509971 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (57511961437 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_53 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82255442519889 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230048247043 / 10000000000000 : ℝ))
      (E := (cell12327 ⟨53, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82255442519889 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230048247043 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_54 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (5138851840139 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300486444863 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨54, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (5138851840139 / 6250000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300486444863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_55 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41093919879363 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287561304627 / 12500000000000 : ℝ))
      (E := (cell12327 ⟨55, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41093919879363 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (287561304627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_56 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41077036720659 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300494443923 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨56, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41077036720659 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300494443923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_57 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82120330462061 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300498462407 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨57, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82120330462061 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300498462407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_58 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (82086610793157 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300502429953 / 100000000000000 : ℝ))
      (E := (cell12327 ⟨58, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (82086610793157 / 100000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (2300502429953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12327_59 : CellCertificate 12327 (448706880037779 / 5000000000000000 : ℝ) (1703953733500653 / 1000000000000000000 : ℝ) (172223456320573 / 5000000000000000 : ℝ)
    (cell12327 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · norm_num [cell12327]
  · have h := gap_lower (n := 12327) (a := (41026457203473 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230050646121 / 10000000000000 : ℝ))
      (E := (cell12327 ⟨59, by decide⟩).energy) (xi := (172223456320573 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12327 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12327]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12327])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12327) (a := (41026457203473 / 50000000000000 : ℝ)) (b := (6686401351 / 4000000000000 : ℝ)) (q := (230050646121 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12327])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12327]

theorem cert12328_40 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (8269715142129 / 10000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150144662251 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨40, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (8269715142129 / 10000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150144662251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_41 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82663031915699 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (35942083381 / 1562500000000 : ℝ))
      (E := (cell12328 ⟨41, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82663031915699 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (35942083381 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_42 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20657234045507 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150148663727 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨42, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20657234045507 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150148663727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_43 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (16518972838059 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300301356253 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨43, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (16518972838059 / 20000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300301356253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_44 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (5160050994417 / 6250000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300305304779 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨44, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (5160050994417 / 6250000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300305304779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_45 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82526791313479 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460061869753 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨45, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82526791313479 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460061869753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_46 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82492790369187 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150156655449 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨46, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82492790369187 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150156655449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_47 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (2576837907763 / 3125000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150158653871 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨47, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (2576837907763 / 3125000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150158653871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_48 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41212429660967 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150160669017 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨48, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41212429660967 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150160669017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_49 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82390929160657 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575081335343 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨49, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82390929160657 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575081335343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_50 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41178511267823 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150164657997 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨50, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41178511267823 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150164657997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_51 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82323139418107 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (230033331889 / 10000000000000 : ℝ))
      (E := (cell12328 ⟨51, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82323139418107 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (230033331889 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_52 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82289279779393 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575084322237 / 25000000000000 : ℝ))
      (E := (cell12328 ⟨52, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82289279779393 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (575084322237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_53 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82255443590999 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300341282779 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨53, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82255443590999 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300341282779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_54 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (20555407706141 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300345297837 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨54, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (20555407706141 / 25000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300345297837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_55 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82187841451869 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150174665683 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨55, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82187841451869 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150174665683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_56 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41077037722417 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460070664263 / 20000000000000 : ℝ))
      (E := (cell12328 ⟨56, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41077037722417 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (460070664263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_57 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82120332775523 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150178661773 / 50000000000000 : ℝ))
      (E := (cell12328 ⟨57, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82120332775523 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (1150178661773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_58 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (82086613416139 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300361275539 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨58, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (82086613416139 / 100000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300361275539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12328_59 : CellCertificate 12328 (44869208862537 / 500000000000000 : ℝ) (425953867125983 / 250000000000000000 : ℝ) (43052279657663 / 1250000000000000 : ℝ)
    (cell12328 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · norm_num [cell12328]
  · have h := gap_lower (n := 12328) (a := (41026458669511 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300365291947 / 100000000000000 : ℝ))
      (E := (cell12328 ⟨59, by decide⟩).energy) (xi := (43052279657663 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12328 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12328]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12328])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12328) (a := (41026458669511 / 50000000000000 : ℝ)) (b := (83573148003 / 50000000000000 : ℝ)) (q := (2300365291947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12328])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12328]

theorem cert12329_40 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (20674287102009 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (115007413051 / 5000000000000 : ℝ))
      (E := (cell12329 ⟨40, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (20674287102009 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (115007413051 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_41 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82663029219277 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575038061307 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨41, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82663029219277 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575038061307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_42 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82628933801999 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300156268097 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨42, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82628933801999 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300156268097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_43 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41297431063111 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150080135337 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨43, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41297431063111 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150080135337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_44 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82560814162117 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460032850499 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨44, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82560814162117 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460032850499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_45 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (41263394940003 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575042067927 / 25000000000000 : ℝ))
      (E := (cell12329 ⟨45, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (41263394940003 / 50000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (575042067927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_46 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82492789250361 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230017226863 / 10000000000000 : ℝ))
      (E := (cell12329 ⟨46, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82492789250361 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (230017226863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_47 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82458812243803 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460035248429 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨47, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82458812243803 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460035248429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_48 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (824248588311 / 1000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150090124909 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨48, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (824248588311 / 1000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150090124909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_49 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (643679132681 / 781250000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (143761514453 / 6250000000000 : ℝ))
      (E := (cell12329 ⟨49, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (643679132681 / 781250000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (143761514453 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_50 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82357022671069 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460037648723 / 20000000000000 : ℝ))
      (E := (cell12329 ⟨50, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82357022671069 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (460037648723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_51 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (20580784966503 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150096113021 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨51, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (20580784966503 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150096113021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_52 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82289280539349 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300196235329 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨52, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82289280539349 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300196235329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_53 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (5140965291411 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300200210127 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨53, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (5140965291411 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300200210127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_54 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (20555408051833 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150102103429 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨54, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (20555408051833 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150102103429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_55 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82187843145399 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150104111383 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨55, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82187843145399 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150104111383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_56 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82154077448699 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300212254883 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨56, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82154077448699 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300212254883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_57 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (5132520943081 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150108120461 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨57, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (5132520943081 / 6250000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150108120461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_58 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (82086616039393 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300220236561 / 100000000000000 : ℝ))
      (E := (cell12329 ⟨58, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (82086616039393 / 100000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (2300220236561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12329_59 : CellCertificate 12329 (179470919809459 / 2000000000000000 : ℝ) (1703677225944037 / 1000000000000000000 : ℝ) (43048695845831 / 1250000000000000 : ℝ)
    (cell12329 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · norm_num [cell12329]
  · have h := gap_lower (n := 12329) (a := (20513230067833 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150112119103 / 50000000000000 : ℝ))
      (E := (cell12329 ⟨59, by decide⟩).energy) (xi := (43048695845831 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12329 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12329]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12329])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12329) (a := (20513230067833 / 25000000000000 : ℝ)) (b := (167132560523 / 100000000000000 : ℝ)) (q := (1150112119103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12329])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12329]

theorem cert12330_40 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41348572697879 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287500906587 / 12500000000000 : ℝ))
      (E := (cell12330 ⟨40, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41348572697879 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287500906587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_41 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82663026523791 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (230001126803 / 10000000000000 : ℝ))
      (E := (cell12330 ⟨41, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82663026523791 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (230001126803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_42 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82628931422867 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300015264027 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨42, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82628931422867 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300015264027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_43 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41297430031503 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150009620223 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨43, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41297430031503 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150009620223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_44 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (4128040620719 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150011627813 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨44, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (4128040620719 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150011627813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_45 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (5157924277957 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300027250129 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨45, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (5157924277957 / 6250000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300027250129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_46 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (3299711525291 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300031223053 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨46, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (3299711525291 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300031223053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_47 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82458811439889 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575008808039 / 25000000000000 : ℝ))
      (E := (cell12330 ⟨47, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82458811439889 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575008808039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_48 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (3296994333637 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (92001568691 / 4000000000000 : ℝ))
      (E := (cell12330 ⟨48, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (3296994333637 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (92001568691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_49 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (823909288063 / 1000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (115002161789 / 5000000000000 : ℝ))
      (E := (cell12330 ⟨49, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (823909288063 / 1000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (115002161789 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_50 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (3294280912283 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150023613517 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨50, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (3294280912283 / 4000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150023613517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_51 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82323140314461 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287506406003 / 12500000000000 : ℝ))
      (E := (cell12330 ⟨51, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82323140314461 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287506406003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_52 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82289281299809 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575013809409 / 25000000000000 : ℝ))
      (E := (cell12330 ⟨52, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82289281299809 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575013809409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_53 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41127722867309 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287507399183 / 12500000000000 : ℝ))
      (E := (cell12330 ⟨53, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41127722867309 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (287507399183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_54 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82221633590527 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300063230971 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨54, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82221633590527 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300063230971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_55 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (82187844839317 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300067229343 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨55, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (82187844839317 / 100000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300067229343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_56 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (41077039726457 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575017811157 / 25000000000000 : ℝ))
      (E := (cell12330 ⟨56, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (41077039726457 / 50000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (575017811157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_57 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (4106016870169 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (115003760727 / 5000000000000 : ℝ))
      (E := (cell12330 ⟨57, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (4106016870169 / 5000000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (115003760727 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_58 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (2052165466573 / 2500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300079194753 / 100000000000000 : ℝ))
      (E := (cell12330 ⟨58, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (2052165466573 / 2500000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (2300079194753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12330_59 : CellCertificate 12330 (89732502546409 / 1000000000000000 : ℝ) (1703539005815507 / 1000000000000000000 : ℝ) (86090225288943 / 2500000000000000 : ℝ)
    (cell12330 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · norm_num [cell12330]
  · have h := gap_lower (n := 12330) (a := (656423385631 / 800000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150041620417 / 50000000000000 : ℝ))
      (E := (cell12330 ⟨59, by decide⟩).energy) (xi := (86090225288943 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12330 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12330]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12330])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12330) (a := (656423385631 / 800000000000 : ℝ)) (b := (167118827323 / 100000000000000 : ℝ)) (q := (1150041620417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12330])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12330]

theorem cert12331_40 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (16539428476891 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299866299531 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨40, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (16539428476891 / 20000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299866299531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_41 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82663023829241 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299870287319 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨41, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82663023829241 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299870287319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_42 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82628929044631 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299874315243 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨42, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82628929044631 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299874315243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_43 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41297429000323 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299878324349 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨43, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41297429000323 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299878324349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_44 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (4128040533373 / 5000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574970578543 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨44, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (4128040533373 / 5000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574970578543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_45 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20631696753849 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299886284029 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨45, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20631696753849 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299886284029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_46 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82492787014927 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (229989029187 / 10000000000000 : ℝ))
      (E := (cell12331 ⟨46, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82492787014927 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (229989029187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_47 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (3298352425467 / 4000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574973569443 / 25000000000000 : ℝ))
      (E := (cell12331 ⟨47, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (3298352425467 / 4000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (574973569443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_48 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20606214462853 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149949149649 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨48, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20606214462853 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149949149649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_49 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82390928630053 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149951148023 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨49, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82390928630053 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149951148023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_50 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (5147313933979 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299906266249 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨50, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (5147313933979 / 6250000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299906266249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_51 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (82323140763453 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299910266897 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨51, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (82323140763453 / 100000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299910266897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_52 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41144641030387 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149957147933 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨52, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41144641030387 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149957147933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_53 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (658043574457 / 800000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459983658361 / 20000000000000 : ℝ))
      (E := (cell12331 ⟨53, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (658043574457 / 800000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (459983658361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_54 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20555408743537 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149961155567 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨54, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20555408743537 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149961155567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_55 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (10273480816703 / 12500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149963146017 / 50000000000000 : ℝ))
      (E := (cell12331 ⟨55, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (10273480816703 / 12500000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (1149963146017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_56 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41077040728739 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299930290551 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨56, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41077040728739 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299930290551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_57 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41060169858887 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299934303509 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨57, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41060169858887 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299934303509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_58 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (41043310643359 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299938268383 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨58, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (41043310643359 / 50000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299938268383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12331_59 : CellCertificate 12331 (89729545649999 / 1000000000000000 : ℝ) (851700404056441 / 500000000000000000 : ℝ) (43041530053409 / 1250000000000000 : ℝ)
    (cell12331 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · norm_num [cell12331]
  · have h := gap_lower (n := 12331) (a := (20513231534163 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299942299827 / 100000000000000 : ℝ))
      (E := (cell12331 ⟨59, by decide⟩).energy) (xi := (43041530053409 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12331 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12331]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12331])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12331) (a := (20513231534163 / 25000000000000 : ℝ)) (b := (20888137051 / 12500000000000 : ℝ)) (q := (2299942299827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12331])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12331]

theorem cert12332_40 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82697139374127 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299725460237 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨40, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82697139374127 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299725460237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_41 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41331510567813 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287466177571 / 12500000000000 : ℝ))
      (E := (cell12332 ⟨41, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41331510567813 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287466177571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_42 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (8262892666729 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299733421749 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨42, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (8262892666729 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299733421749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_43 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82594855939143 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149868731803 / 50000000000000 : ℝ))
      (E := (cell12332 ⟨43, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82594855939143 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (1149868731803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_44 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82560808921357 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459948285627 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨44, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82560808921357 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459948285627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_45 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41263392792129 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299745432237 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨45, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41263392792129 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299745432237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_46 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41246392949159 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299749416231 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨46, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41246392949159 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299749416231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_47 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82458809834161 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143734589867 / 6250000000000 : ℝ))
      (E := (cell12332 ⟨47, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82458809834161 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143734589867 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_48 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41212428681279 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459951487399 / 20000000000000 : ℝ))
      (E := (cell12332 ⟨48, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41212428681279 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (459951487399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_49 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (20597732113607 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299761412047 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨49, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (20597732113607 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299761412047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_50 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41178511540417 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (229976542021 / 10000000000000 : ℝ))
      (E := (cell12332 ⟨50, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41178511540417 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (229976542021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_51 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82323141212987 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299769400603 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨51, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82323141212987 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299769400603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_52 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82289282822243 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299773410023 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨52, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82289282822243 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299773410023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_53 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41127723940049 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287472180767 / 12500000000000 : ℝ))
      (E := (cell12332 ⟨53, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41127723940049 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (287472180767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_54 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (16444327271639 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299781388313 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨54, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (16444327271639 / 20000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299781388313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_55 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41093924114159 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299785410843 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨55, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41093924114159 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299785410843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_56 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (8215408346239 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143736837041 / 6250000000000 : ℝ))
      (E := (cell12332 ⟨56, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (8215408346239 / 10000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (143736837041 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_57 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (82120342032479 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (229979338961 / 10000000000000 : ℝ))
      (E := (cell12332 ⟨57, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (82120342032479 / 100000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (229979338961 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_58 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (20521655977697 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299797398321 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨58, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (20521655977697 / 25000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299797398321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12332_59 : CellCertificate 12332 (448632946076931 / 5000000000000000 : ℝ) (340652526566141 / 200000000000000000 : ℝ) (344303584579743 / 10000000000000000 : ℝ)
    (cell12332 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · norm_num [cell12332]
  · have h := gap_lower (n := 12332) (a := (41026464534831 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299801415191 / 100000000000000 : ℝ))
      (E := (cell12332 ⟨59, by decide⟩).energy) (xi := (344303584579743 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12332 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12332]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12332])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12332) (a := (41026464534831 / 50000000000000 : ℝ)) (b := (6683654711 / 4000000000000 : ℝ)) (q := (2299801415191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12332])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12332]

theorem cert12333_40 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41348568182387 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299584676103 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨40, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41348568182387 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299584676103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_41 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41331509221473 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (91983546711 / 4000000000000 : ℝ))
      (E := (cell12333 ⟨41, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41331509221473 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (91983546711 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_42 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41314462145423 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (22995926423 / 1000000000000 : ℝ))
      (E := (cell12333 ⟨42, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41314462145423 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (22995926423 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_43 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (2581089183703 / 3125000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459919331643 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨43, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (2581089183703 / 3125000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459919331643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_44 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (10320100897009 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149800328159 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨44, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (10320100897009 / 12500000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149800328159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_45 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82526784153897 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149802317963 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨45, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82526784153897 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149802317963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_46 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82492784782447 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299608654989 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨46, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82492784782447 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299608654989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_47 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (16491761806469 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (114980632679 / 5000000000000 : ℝ))
      (E := (cell12333 ⟨47, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (16491761806469 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (114980632679 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_48 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20606214218591 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299616630363 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨48, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20606214218591 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299616630363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_49 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82390928279423 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299620642707 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨49, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82390928279423 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299620642707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_50 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41178511609293 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299624629971 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨50, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41178511609293 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299624629971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_51 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (16464628332613 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (114981432457 / 5000000000000 : ℝ))
      (E := (cell12333 ⟨51, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (16464628332613 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (114981432457 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_52 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (16457856716843 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299632639099 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨52, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (16457856716843 / 20000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299632639099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_53 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (1285241389899 / 1562500000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (7186364367 / 312500000000 : ℝ))
      (E := (cell12333 ⟨53, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (1285241389899 / 1562500000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (7186364367 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_54 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82221637742669 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149820319811 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨54, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82221637742669 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149820319811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_55 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (82187849923399 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299644644831 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨55, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (82187849923399 / 100000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299644644831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_56 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (20538521366913 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (91985944401 / 4000000000000 : ℝ))
      (E := (cell12333 ⟨56, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (20538521366913 / 25000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (91985944401 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_57 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41060172173747 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459930518213 / 20000000000000 : ℝ))
      (E := (cell12333 ⟨57, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41060172173747 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (459930518213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_58 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (8208662653513 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299656643697 / 100000000000000 : ℝ))
      (E := (cell12333 ⟨58, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (8208662653513 / 10000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (2299656643697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12333_59 : CellCertificate 12333 (448618166212287 / 5000000000000000 : ℝ) (1703124479963521 / 1000000000000000000 : ℝ) (43034366701473 / 1250000000000000 : ℝ)
    (cell12333 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · norm_num [cell12333]
  · have h := gap_lower (n := 12333) (a := (41026466001453 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149830293461 / 50000000000000 : ℝ))
      (E := (cell12333 ⟨59, by decide⟩).energy) (xi := (43034366701473 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12333 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12333]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12333])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12333) (a := (41026466001453 / 50000000000000 : ℝ)) (b := (83538820713 / 50000000000000 : ℝ)) (q := (1149830293461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12333])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12333]

theorem cert12334_40 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41348566678197 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459888789427 / 20000000000000 : ℝ))
      (E := (cell12334 ⟨40, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41348566678197 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (459888789427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_41 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82663015751201 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574861977869 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨41, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82663015751201 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574861977869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_42 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82628921915297 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299451918143 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨42, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82628921915297 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299451918143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_43 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16518970363741 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299455908179 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨43, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16518970363741 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299455908179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_44 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41280402715801 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149729969961 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨44, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41280402715801 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149729969961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_45 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82526782724313 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994638951 / 1000000000000 : ℝ))
      (E := (cell12334 ⟨45, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82526782724313 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994638951 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_46 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41246391833657 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149733945221 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨46, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41246391833657 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149733945221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_47 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (20614702057807 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994719249 / 1000000000000 : ℝ))
      (E := (cell12334 ⟨47, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (20614702057807 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (22994719249 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_48 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (8242485638683 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149737939703 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨48, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (8242485638683 / 10000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149737939703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_49 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41195464052519 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149739964553 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨49, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41195464052519 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149739964553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_50 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (2058925583923 / 2500000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299483895533 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨50, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (2058925583923 / 2500000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299483895533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_51 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (16464628422737 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (91979515783 / 4000000000000 : ℝ))
      (E := (cell12334 ⟨51, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (16464628422737 / 20000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (91979515783 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_52 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (20572321086673 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287436490513 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨52, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (20572321086673 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287436490513 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_53 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41127725013719 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (229949592277 / 10000000000000 : ℝ))
      (E := (cell12334 ⟨53, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41127725013719 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (229949592277 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_54 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82221639127569 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299499887949 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨54, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82221639127569 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299499887949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_55 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (20546962904717 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (18396031007 / 800000000000 : ℝ))
      (E := (cell12334 ⟨55, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (20546962904717 / 25000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (18396031007 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_56 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41077043736631 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149753941789 / 50000000000000 : ℝ))
      (E := (cell12334 ⟨56, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41077043736631 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (1149753941789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_57 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82120346662819 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574877976969 / 25000000000000 : ℝ))
      (E := (cell12334 ⟨57, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82120346662819 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (574877976969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_58 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (82086629159743 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299515886249 / 100000000000000 : ℝ))
      (E := (cell12334 ⟨58, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (82086629159743 / 100000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (2299515886249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12334_59 : CellCertificate 12334 (897206777310991 / 10000000000000000 : ℝ) (13623890796047 / 8000000000000000 : ℝ) (43030785940249 / 1250000000000000 : ℝ)
    (cell12334 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · norm_num [cell12334]
  · have h := gap_lower (n := 12334) (a := (41026467468191 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287439984273 / 12500000000000 : ℝ))
      (E := (cell12334 ⟨59, by decide⟩).energy) (xi := (43030785940249 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12334 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12334]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12334])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12334) (a := (41026467468191 / 50000000000000 : ℝ)) (b := (83531958679 / 50000000000000 : ℝ)) (q := (287439984273 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12334])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12334]

theorem cert12335_40 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82697130348989 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299303273329 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨40, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82697130348989 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299303273329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_41 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (8266301306039 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (114965363457 / 5000000000000 : ℝ))
      (E := (cell12335 ⟨41, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (8266301306039 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (114965363457 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_42 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41314459770321 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299311249279 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨42, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41314459770321 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299311249279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_43 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (8259484975977 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299315272281 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨43, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (8259484975977 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299315272281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_44 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82560803687949 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149659639473 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨44, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82560803687949 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149659639473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_45 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41263390647753 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459864653717 / 20000000000000 : ℝ))
      (E := (cell12335 ⟨45, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41263390647753 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (459864653717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_46 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41246391276459 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287415905037 / 12500000000000 : ℝ))
      (E := (cell12335 ⟨46, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41246391276459 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (287415905037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_47 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (8245880743081 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299331251831 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨47, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (8245880743081 / 10000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299331251831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_48 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16484971179991 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (143708452689 / 6250000000000 : ℝ))
      (E := (cell12335 ⟨48, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16484971179991 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (143708452689 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_49 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (3295637117251 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149669635621 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨49, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (3295637117251 / 4000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149669635621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_50 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16471404699167 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149671608449 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨50, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16471404699167 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149671608449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_51 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (5145196410303 / 6250000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574836813711 / 25000000000000 : ℝ))
      (E := (cell12335 ⟨51, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (5145196410303 / 6250000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574836813711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_52 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82289285109671 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (28741890813 / 1250000000000 : ℝ))
      (E := (cell12335 ⟨52, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82289285109671 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (28741890813 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_53 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (41127725550903 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574838811269 / 25000000000000 : ℝ))
      (E := (cell12335 ⟨53, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (41127725550903 / 50000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574838811269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_54 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (16444328102579 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299359251371 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨54, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (16444328102579 / 20000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299359251371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_55 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20546963328681 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299363222103 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨55, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20546963328681 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299363222103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_56 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82154089479221 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149683606657 / 50000000000000 : ℝ))
      (E := (cell12335 ⟨56, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82154089479221 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (1149683606657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_57 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82120348978453 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (35927675341 / 1562500000000 : ℝ))
      (E := (cell12335 ⟨57, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82120348978453 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (35927675341 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_58 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (20521657946157 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574843811061 / 25000000000000 : ℝ))
      (E := (cell12335 ⟨58, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (20521657946157 / 25000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (574843811061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12335_59 : CellCertificate 12335 (448588613405991 / 5000000000000000 : ℝ) (425712060363079 / 250000000000000000 : ℝ) (86054411577241 / 2500000000000000 : ℝ)
    (cell12335 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · norm_num [cell12335]
  · have h := gap_lower (n := 12335) (a := (82052937870091 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299379217819 / 100000000000000 : ℝ))
      (E := (cell12335 ⟨59, by decide⟩).energy) (xi := (86054411577241 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12335 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12335]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12335])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12335) (a := (82052937870091 / 100000000000000 : ℝ)) (b := (167050195571 / 100000000000000 : ℝ)) (q := (2299379217819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12335])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12335]

theorem cert12336_40 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41348563671279 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (11495813567 / 500000000000 : ℝ))
      (E := (cell12336 ⟨40, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41348563671279 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (11495813567 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_41 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41331505185257 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (143697917627 / 6250000000000 : ℝ))
      (E := (cell12336 ⟨41, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41331505185257 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (143697917627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_42 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82628917166883 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149585347233 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨42, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82628917166883 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149585347233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_43 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (8259484770169 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299174691741 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨43, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (8259484770169 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299174691741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_44 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (10320100243139 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299178673391 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨44, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (10320100243139 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299178673391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_45 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (20631694966869 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574795674389 / 25000000000000 : ℝ))
      (E := (cell12336 ⟨45, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (20631694966869 / 25000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574795674389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_46 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (4124639071963 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149593322849 / 50000000000000 : ℝ))
      (E := (cell12336 ⟨46, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (4124639071963 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (1149593322849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_47 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (8245880663109 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (9196762773 / 400000000000 : ℝ))
      (E := (cell12336 ⟨47, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (8245880663109 / 10000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (9196762773 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_48 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (4121242770687 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299194662317 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨48, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (4121242770687 / 5000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299194662317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_49 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82390927758131 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (7184995841 / 312500000000 : ℝ))
      (E := (cell12336 ⟨49, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82390927758131 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (7184995841 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_50 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82357023635331 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299202653013 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨50, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82357023635331 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299202653013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_51 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82323143016553 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299206670981 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨51, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82323143016553 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299206670981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_52 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (16457857174631 / 20000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459842132381 / 20000000000000 : ℝ))
      (E := (cell12336 ⟨52, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (16457857174631 / 20000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (459842132381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_53 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41127726088319 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287401835299 / 12500000000000 : ℝ))
      (E := (cell12336 ⟨53, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41127726088319 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287401835299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_54 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41110820949323 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574804667713 / 25000000000000 : ℝ))
      (E := (cell12336 ⟨54, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41110820949323 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (574804667713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_55 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82187855010967 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299222624451 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨55, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82187855010967 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299222624451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_56 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (10269261435691 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (28740333229 / 1250000000000 : ℝ))
      (E := (cell12336 ⟨56, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (10269261435691 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (28740333229 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_57 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (41060175647199 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287403831391 / 12500000000000 : ℝ))
      (E := (cell12336 ⟨57, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (41060175647199 / 50000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287403831391 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_58 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (10260829301223 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299234658549 / 100000000000000 : ℝ))
      (E := (cell12336 ⟨58, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (10260829301223 / 12500000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (2299234658549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12336_59 : CellCertificate 12336 (56071730057901 / 625000000000000 : ℝ) (1702710155797393 / 1000000000000000000 : ℝ) (344189009971301 / 10000000000000000 : ℝ)
    (cell12336 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · norm_num [cell12336]
  · have h := gap_lower (n := 12336) (a := (82052940804033 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287404834623 / 12500000000000 : ℝ))
      (E := (cell12336 ⟨59, by decide⟩).energy) (xi := (344189009971301 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12336 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12336]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12336])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12336) (a := (82052940804033 / 100000000000000 : ℝ)) (b := (33407295213 / 20000000000000 : ℝ)) (q := (287404834623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12336])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12336]

theorem cert12337_40 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (826971243371 / 1000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (91960885997 / 4000000000000 : ℝ))
      (E := (cell12337 ⟨40, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (826971243371 / 1000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (91960885997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_41 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82663007681571 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574756537539 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨41, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82663007681571 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574756537539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_42 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41314457397009 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299030136189 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨42, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41314457397009 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299030136189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_43 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (16518969128893 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299034166559 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨43, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (16518969128893 / 20000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299034166559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_44 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (8256080020309 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299038182063 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨44, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (8256080020309 / 10000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299038182063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_45 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82526778440223 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574760545503 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨45, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82526778440223 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574760545503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_46 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (4124639016317 / 5000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299046165501 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨46, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (4124639016317 / 5000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299046165501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_47 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (20614701458017 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299050131407 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨47, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (20614701458017 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299050131407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_48 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82424854928183 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299054137289 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨48, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82424854928183 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299054137289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_49 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82390927585607 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149529061369 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨49, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82390927585607 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149529061369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_50 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (5147313985963 / 6250000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574765536233 / 25000000000000 : ℝ))
      (E := (cell12337 ⟨50, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (5147313985963 / 6250000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (574765536233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_51 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (12862991167 / 15625000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459813228597 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨51, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (12862991167 / 15625000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459813228597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_52 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82289286637141 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149535057351 / 50000000000000 : ℝ))
      (E := (cell12337 ⟨52, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82289286637141 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (1149535057351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_53 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (41127726625967 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299074116687 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨53, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (41127726625967 / 50000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299074116687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_54 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82221643284823 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229907814639 / 10000000000000 : ℝ))
      (E := (cell12337 ⟨54, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82221643284823 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (229907814639 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_55 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82187856707597 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299082141983 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨55, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82187856707597 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299082141983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_56 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (10269261686523 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299086159511 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨56, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (10269261686523 / 12500000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299086159511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_57 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (20530088402663 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299090136681 / 100000000000000 : ℝ))
      (E := (cell12337 ⟨57, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (20530088402663 / 25000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (2299090136681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_58 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (82086637035211 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459818825833 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨58, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (82086637035211 / 100000000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459818825833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12337_59 : CellCertificate 12337 (22427953491329 / 250000000000000 : ℝ) (851286046267829 / 500000000000000000 : ℝ) (172080189253801 / 5000000000000000 : ℝ)
    (cell12337 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · norm_num [cell12337]
  · have h := gap_lower (n := 12337) (a := (2564154491819 / 3125000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459819626673 / 20000000000000 : ℝ))
      (E := (cell12337 ⟨59, by decide⟩).energy) (xi := (172080189253801 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12337 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12337]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12337])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12337) (a := (2564154491819 / 3125000000000 : ℝ)) (b := (4175568971 / 2500000000000 : ℝ)) (q := (459819626673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12337])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12337]

theorem cert12338_40 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16539424266523 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298881700331 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨40, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16539424266523 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298881700331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_41 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82663004993563 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459777146449 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨41, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82663004993563 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459777146449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_42 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82628912422047 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149444845983 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨42, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82628912422047 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149444845983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_43 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16518968717619 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298893696737 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨43, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16518968717619 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298893696737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_44 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20640199615471 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459779537471 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨44, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20640199615471 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459779537471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_45 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16505355402749 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298901721957 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨45, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16505355402749 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298901721957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_46 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20623194803539 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459781136401 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨46, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20623194803539 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459781136401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_47 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (5153675314609 / 6250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459781936811 / 20000000000000 : ℝ))
      (E := (cell12338 ⟨47, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (5153675314609 / 6250000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (459781936811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_48 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16484970888657 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149456863419 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨48, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16484970888657 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149456863419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_49 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82390927413703 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149458845511 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨49, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82390927413703 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149458845511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_50 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41178511958033 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298921692657 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨50, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41178511958033 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298921692657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_51 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (20580785980397 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298925670861 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨51, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (20580785980397 / 25000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298925670861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_52 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (8228928740163 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149464841213 / 50000000000000 : ℝ))
      (E := (cell12338 ⟨52, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (8228928740163 / 10000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (1149464841213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_53 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41127727163847 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298933725013 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨53, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41127727163847 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298933725013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_54 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41110822335713 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574734419497 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨54, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41110822335713 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574734419497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_55 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (41093929202307 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (57473542891 / 2500000000000 : ℝ))
      (E := (cell12338 ⟨55, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (41093929202307 / 50000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (57473542891 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_56 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82154095499187 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298945716889 / 100000000000000 : ℝ))
      (E := (cell12338 ⟨56, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82154095499187 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (2298945716889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_57 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16424071185443 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574737419621 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨57, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16424071185443 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574737419621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_58 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (82086639660909 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574738428807 / 25000000000000 : ℝ))
      (E := (cell12338 ⟨58, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (82086639660909 / 100000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (574738428807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12338_59 : CellCertificate 12338 (897088602991083 / 10000000000000000 : ℝ) (1702434051661663 / 1000000000000000000 : ℝ) (344131751916467 / 10000000000000000 : ℝ)
    (cell12338 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · norm_num [cell12338]
  · have h := gap_lower (n := 12338) (a := (16410589334523 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (7184242829 / 312500000000 : ℝ))
      (E := (cell12338 ⟨59, by decide⟩).energy) (xi := (344131751916467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12338 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12338]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12338])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12338) (a := (16410589334523 / 20000000000000 : ℝ)) (b := (83504521947 / 50000000000000 : ℝ)) (q := (7184242829 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12338])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12338]

theorem cert12339_40 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82697118329103 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287342670577 / 12500000000000 : ℝ))
      (E := (cell12339 ⟨40, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82697118329103 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287342670577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_41 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82663002306487 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (71835792799 / 3125000000000 : ℝ))
      (E := (cell12339 ⟨41, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82663002306487 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (71835792799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_42 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (8262891005097 / 10000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298749361799 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨42, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (8262891005097 / 10000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298749361799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_43 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82594841532579 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298753341059 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨43, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82594841532579 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298753341059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_44 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41280398360747 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298757365681 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨44, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41280398360747 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298757365681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_45 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (20631693897011 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229876131739 / 10000000000000 : ℝ))
      (E := (cell12339 ⟨45, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (20631693897011 / 25000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229876131739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_46 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82492778102709 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298765312913 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨46, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82492778102709 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298765312913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_47 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41229402118059 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459753870239 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨47, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41229402118059 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459753870239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_48 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41212426979523 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (143673332073 / 6250000000000 : ℝ))
      (E := (cell12339 ⟨48, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41212426979523 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (143673332073 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_49 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41195463621209 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298777315049 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨49, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41195463621209 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298777315049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_50 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (10294628007163 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229878129619 / 10000000000000 : ℝ))
      (E := (cell12339 ⟨50, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (10294628007163 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (229878129619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_51 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41161572187459 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287348164197 / 12500000000000 : ℝ))
      (E := (cell12339 ⟨51, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41161572187459 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287348164197 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_52 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41144644083311 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574697326521 / 25000000000000 : ℝ))
      (E := (cell12339 ⟨52, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41144644083311 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (574697326521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_53 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41127727701959 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298793330319 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨53, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41127727701959 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298793330319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_54 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82221646058453 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (143674832793 / 6250000000000 : ℝ))
      (E := (cell12339 ⟨54, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82221646058453 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (143674832793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_55 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82187860102017 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (114940067271 / 5000000000000 : ℝ))
      (E := (cell12339 ⟨55, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82187860102017 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (114940067271 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_56 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41077048753269 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459761066091 / 20000000000000 : ℝ))
      (E := (cell12339 ⟨56, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41077048753269 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (459761066091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_57 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (10265044780511 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (71837791739 / 3125000000000 : ℝ))
      (E := (cell12339 ⟨57, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (10265044780511 / 12500000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (71837791739 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_58 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (82086642286877 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287351662309 / 12500000000000 : ℝ))
      (E := (cell12339 ⟨58, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (82086642286877 / 100000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (287351662309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12339_59 : CellCertificate 12339 (448529535469527 / 5000000000000000 : ℝ) (340459206633993 / 200000000000000000 : ℝ) (172051565098249 / 5000000000000000 : ℝ)
    (cell12339 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · norm_num [cell12339]
  · have h := gap_lower (n := 12339) (a := (41026474803627 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298817333573 / 100000000000000 : ℝ))
      (E := (cell12339 ⟨59, by decide⟩).energy) (xi := (172051565098249 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12339 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12339]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12339])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12339) (a := (41026474803627 / 50000000000000 : ℝ)) (b := (166995331227 / 100000000000000 : ℝ)) (q := (2298817333573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12339])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12339]

theorem cert12340_40 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20674278831641 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (28732512817 / 1250000000000 : ℝ))
      (E := (cell12340 ⟨40, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20674278831641 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (28732512817 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_41 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (16532599924069 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149302531063 / 50000000000000 : ℝ))
      (E := (cell12340 ⟨41, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (16532599924069 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149302531063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_42 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82628907680787 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298609028173 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨42, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82628907680787 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298609028173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_43 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41297419738959 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149306520371 / 50000000000000 : ℝ))
      (E := (cell12340 ⟨43, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41297419738959 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (1149306520371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_44 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41280397490959 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298617040629 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨44, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41280397490959 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298617040629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_45 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41263387081559 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298621027143 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨45, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41263387081559 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298621027143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_46 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41246388495999 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298624999377 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨46, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41246388495999 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298624999377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_47 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20614700859797 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298629015079 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨47, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20614700859797 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298629015079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_48 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (16484970695093 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (7183228169 / 312500000000 : ℝ))
      (E := (cell12340 ⟨48, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (16484970695093 / 20000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (7183228169 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_49 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82390927071753 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298636994821 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨49, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82390927071753 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298636994821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_50 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41178512099561 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298641014479 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨50, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41178512099561 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298641014479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_51 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (8232314482879 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574661253041 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨51, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (8232314482879 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574661253041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_52 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20572322233029 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298649044671 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨52, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20572322233029 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298649044671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_53 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41127728240303 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287331623953 / 12500000000000 : ℝ))
      (E := (cell12340 ⟨53, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41127728240303 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (287331623953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_54 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41110823722953 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (45973140549 / 2000000000000 : ℝ))
      (E := (cell12340 ⟨54, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41110823722953 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (45973140549 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_55 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (41093930899903 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298661031327 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨55, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (41093930899903 / 50000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298661031327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_56 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (82154099514237 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298665000209 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨56, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (82154099514237 / 100000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298665000209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_57 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (8212036056127 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (4489587871 / 195312500000 : ℝ))
      (E := (cell12340 ⟨57, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (8212036056127 / 10000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (4489587871 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_58 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (20521661228279 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574668249291 / 25000000000000 : ℝ))
      (E := (cell12340 ⟨58, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (20521661228279 / 25000000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (574668249291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12340_59 : CellCertificate 12340 (112128692936993 / 1250000000000000 : ℝ) (1702158037055119 / 1000000000000000000 : ℝ) (344074513346297 / 10000000000000000 : ℝ)
    (cell12340 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · norm_num [cell12340]
  · have h := gap_lower (n := 12340) (a := (656423620337 / 800000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298677018243 / 100000000000000 : ℝ))
      (E := (cell12340 ⟨59, by decide⟩).energy) (xi := (344074513346297 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12340 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12340]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12340])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12340) (a := (656423620337 / 800000000000 : ℝ)) (b := (83490810419 / 50000000000000 : ℝ)) (q := (2298677018243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12340])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12340]

theorem cert12341_40 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82697112324997 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574615199997 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨40, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82697112324997 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574615199997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_41 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (16532599387027 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (7182702531 / 312500000000 : ℝ))
      (E := (cell12341 ⟨41, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (16532599387027 / 20000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (7182702531 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_42 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82628905311497 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574617202151 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨42, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82628905311497 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574617202151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_43 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (8259483742411 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229847279579 / 10000000000000 : ℝ))
      (E := (cell12341 ⟨43, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (8259483742411 / 10000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (229847279579 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_44 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82560793243157 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (459695354201 / 20000000000000 : ℝ))
      (E := (cell12341 ⟨44, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82560793243157 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (459695354201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_45 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (10315846592371 / 12500000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298480792387 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨45, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (10315846592371 / 12500000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298480792387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_46 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (10311596985253 / 12500000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298484800247 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨46, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (10311596985253 / 12500000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298484800247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_47 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (20614700660739 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298488793457 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨47, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (20614700660739 / 25000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298488793457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_48 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41212426496271 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149246385337 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨48, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41212426496271 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149246385337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_49 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41195463450853 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (143656049329 / 6250000000000 : ℝ))
      (E := (cell12341 ⟨49, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41195463450853 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (143656049329 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_50 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82357024341521 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (71828149643 / 3125000000000 : ℝ))
      (E := (cell12341 ⟨50, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82357024341521 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (71828149643 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_51 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82323145283203 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (71828273957 / 3125000000000 : ℝ))
      (E := (cell12341 ⟨51, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82323145283203 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (71828273957 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_52 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82289289698113 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298508780201 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨52, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82289289698113 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298508780201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_53 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82255457557757 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149256383973 / 50000000000000 : ℝ))
      (E := (cell12341 ⟨53, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82255457557757 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (1149256383973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_54 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82221648833783 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574629196569 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨54, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82221648833783 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574629196569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_55 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82187863497981 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28731509667 / 1250000000000 : ℝ))
      (E := (cell12341 ⟨55, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82187863497981 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (28731509667 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_56 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82154101522283 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298524785241 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨56, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82154101522283 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298524785241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_57 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82120362878761 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298528759621 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨57, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82120362878761 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298528759621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_58 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (41043323769813 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574633188043 / 25000000000000 : ℝ))
      (E := (cell12341 ⟨58, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (41043323769813 / 50000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (574633188043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12341_59 : CellCertificate 12341 (897000020660621 / 10000000000000000 : ℝ) (340404012662337 / 200000000000000000 : ℝ) (344045901364467 / 10000000000000000 : ℝ)
    (cell12341 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · norm_num [cell12341]
  · have h := gap_lower (n := 12341) (a := (82052955477229 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298536759291 / 100000000000000 : ℝ))
      (E := (cell12341 ⟨59, by decide⟩).energy) (xi := (344045901364467 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12341 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12341]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12341])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12341) (a := (82052955477229 / 100000000000000 : ℝ)) (b := (166967912727 / 100000000000000 : ℝ)) (q := (2298536759291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12341])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12341]

theorem cert12342_40 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41348554662201 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574580157447 / 25000000000000 : ℝ))
      (E := (cell12342 ⟨40, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41348554662201 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574580157447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_41 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41331497125429 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (45966492259 / 2000000000000 : ℝ))
      (E := (cell12342 ⟨41, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41331497125429 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (45966492259 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_42 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (826289029431 / 1000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298328644337 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨42, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (826289029431 / 1000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298328644337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_43 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20648708842789 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298332606203 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨43, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20648708842789 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298332606203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_44 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (8256079150521 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459667323123 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨44, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (8256079150521 / 10000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459667323123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_45 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82526771315593 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574585153281 / 25000000000000 : ℝ))
      (E := (cell12342 ⟨45, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82526771315593 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574585153281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_46 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41246387386393 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298344597821 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨46, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41246387386393 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298344597821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_47 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82458801847421 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149174313727 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨47, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82458801847421 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149174313727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_48 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82424852510277 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298352641851 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨48, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82424852510277 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298352641851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_49 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82390926732279 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574589159863 / 25000000000000 : ℝ))
      (E := (cell12342 ⟨49, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82390926732279 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (574589159863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_50 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82357024484499 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459672123697 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨50, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82357024484499 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459672123697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_51 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20580786434539 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (229836463593 / 10000000000000 : ℝ))
      (E := (cell12342 ⟨51, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20580786434539 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (229836463593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_52 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20572322616153 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149184315331 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨52, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20572322616153 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149184315331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_53 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20563864658843 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298372600269 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨53, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20563864658843 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298372600269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_54 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (16444330044417 / 20000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149188300583 / 50000000000000 : ℝ))
      (E := (cell12342 ⟨54, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (16444330044417 / 20000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (1149188300583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_55 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82187865196543 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459676126117 / 20000000000000 : ℝ))
      (E := (cell12342 ⟨55, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82187865196543 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (459676126117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_56 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82154103530677 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298384626463 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨56, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82154103530677 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298384626463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_57 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (82120365196561 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298388585543 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨57, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (82120365196561 / 100000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298388585543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_58 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (41043325083203 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287299077829 / 12500000000000 : ℝ))
      (E := (cell12342 ⟨58, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (41043325083203 / 50000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (287299077829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12342_59 : CellCertificate 12342 (896970502431957 / 10000000000000000 : ℝ) (1701882111934221 / 1000000000000000000 : ℝ) (34401729424961 / 1000000000000000 : ℝ)
    (cell12342 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · norm_num [cell12342]
  · have h := gap_lower (n := 12342) (a := (20513239603141 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298396615879 / 100000000000000 : ℝ))
      (E := (cell12342 ⟨59, by decide⟩).energy) (xi := (34401729424961 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12342 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12342]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12342])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12342) (a := (20513239603141 / 25000000000000 : ℝ)) (b := (166954206893 / 100000000000000 : ℝ)) (q := (2298396615879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12342])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12342]

theorem cert12343_40 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41348553162389 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574545128691 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨40, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41348553162389 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574545128691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_41 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82662991567513 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (459636905991 / 20000000000000 : ℝ))
      (E := (cell12343 ⟨41, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82662991567513 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (459636905991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_42 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (16525780115119 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298188535373 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨42, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (16525780115119 / 20000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298188535373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_43 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (5162177082441 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574548132691 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨43, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (5162177082441 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574548132691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_44 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82560789768077 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287274564457 / 12500000000000 : ℝ))
      (E := (cell12343 ⟨44, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82560789768077 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287274564457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_45 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (644740389789 / 781250000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (459640109637 / 20000000000000 : ℝ))
      (E := (cell12343 ⟨45, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (644740389789 / 781250000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (459640109637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_46 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82492773664283 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298204509807 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨46, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82492773664283 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298204509807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_47 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82458801052583 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298208517073 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨47, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82458801052583 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298208517073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_48 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82424852028669 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149106254907 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨48, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82424852028669 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149106254907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_49 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8239092656347 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298216545391 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨49, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8239092656347 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298216545391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_50 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82357024628057 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149110252103 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨50, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82357024628057 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149110252103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_51 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82323146193651 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114911225107 / 5000000000000 : ℝ))
      (E := (cell12343 ⟨51, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82323146193651 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (114911225107 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_52 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (20572322807903 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287278567133 / 12500000000000 : ℝ))
      (E := (cell12343 ⟨52, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (20572322807903 / 25000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (287278567133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_53 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82255459713449 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574558122149 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨53, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82255459713449 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574558122149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_54 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82221651610811 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298236531163 / 100000000000000 : ℝ))
      (E := (cell12343 ⟨54, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82221651610811 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (2298236531163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_55 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (8218786689549 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149120242437 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨55, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (8218786689549 / 10000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149120242437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_56 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (41077052769709 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149122261939 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨56, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (41077052769709 / 50000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149122261939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_57 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82120367514669 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149124263417 / 50000000000000 : ℝ))
      (E := (cell12343 ⟨57, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82120367514669 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (1149124263417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_58 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (5130415799591 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574563122569 / 25000000000000 : ℝ))
      (E := (cell12343 ⟨58, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (5130415799591 / 6250000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (574563122569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12343_59 : CellCertificate 12343 (448470494404411 / 5000000000000000 : ℝ) (425436045729323 / 250000000000000000 : ℝ) (85997173000083 / 2500000000000000 : ℝ)
    (cell12343 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · norm_num [cell12343]
  · have h := gap_lower (n := 12343) (a := (82052961348131 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (143641033053 / 6250000000000 : ℝ))
      (E := (cell12343 ⟨59, by decide⟩).energy) (xi := (85997173000083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12343 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12343]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12343])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12343) (a := (82052961348131 / 100000000000000 : ℝ)) (b := (33388100667 / 20000000000000 : ℝ)) (q := (143641033053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12343])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12343]

theorem cert12344_40 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41348551663063 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298040513627 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨40, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41348551663063 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298040513627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_41 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (826629888851 / 1000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298044502199 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨41, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (826629888851 / 1000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298044502199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_42 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (10328612276123 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (143628030107 / 6250000000000 : ℝ))
      (E := (cell12344 ⟨42, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (10328612276123 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (143628030107 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_43 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82594831267809 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298052510693 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨43, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82594831267809 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298052510693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_44 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82560788031759 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298056529933 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨44, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82560788031759 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298056529933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_45 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82526768471167 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298060479911 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨45, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82526768471167 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298060479911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_46 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82492772556517 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (45961289547 / 2000000000000 : ℝ))
      (E := (cell12344 ⟨46, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82492772556517 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (45961289547 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_47 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (2061470006461 / 2500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298068521193 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨47, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (2061470006461 / 2500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298068521193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_48 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82424851547719 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298072492363 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨48, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82424851547719 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298072492363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_49 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82390926395279 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298076507079 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨49, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82390926395279 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298076507079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_50 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (16471404954439 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298080504687 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨50, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (16471404954439 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298080504687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_51 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41161573324843 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298084483199 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨51, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41161573324843 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298084483199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_52 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (16457858399823 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459617699881 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨52, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (16457858399823 / 20000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459617699881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_53 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (8225546079199 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298092491943 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨53, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (8225546079199 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298092491943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_54 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41110826499981 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459619291637 / 20000000000000 : ℝ))
      (E := (cell12344 ⟨54, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41110826499981 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (459619291637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_55 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (82187868594823 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149050227179 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨55, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (82187868594823 / 100000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149050227179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_56 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41077053774253 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149052238743 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨56, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41077053774253 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149052238743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_57 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (41060184916543 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574527116317 / 25000000000000 : ℝ))
      (E := (cell12344 ⟨57, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (41060184916543 / 50000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (574527116317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_58 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (10260831927597 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149056236687 / 50000000000000 : ℝ))
      (E := (cell12344 ⟨58, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (10260831927597 / 12500000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (1149056236687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12344_59 : CellCertificate 12344 (896911479790087 / 10000000000000000 : ℝ) (85080313812773 / 50000000000000000 : ℝ) (343960094615237 / 10000000000000000 : ℝ)
    (cell12344 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · norm_num [cell12344]
  · have h := gap_lower (n := 12344) (a := (8205296428393 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298116498199 / 100000000000000 : ℝ))
      (E := (cell12344 ⟨59, by decide⟩).energy) (xi := (343960094615237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12344 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12344]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12344])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12344) (a := (8205296428393 / 10000000000000 : ℝ)) (b := (166926802053 / 100000000000000 : ℝ)) (q := (2298116498199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12344])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12344]

theorem cert12345_40 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16539420065689 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148950283833 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨40, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16539420065689 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148950283833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_41 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82662986203619 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297904529683 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨41, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82662986203619 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297904529683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_42 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16525779168653 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297908542113 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨42, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16525779168653 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297908542113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_43 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16518965843483 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (229791254599 / 10000000000000 : ℝ))
      (E := (cell12345 ⟨43, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16518965843483 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (229791254599 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_44 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41280393148127 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297916540837 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨44, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41280393148127 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297916540837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_45 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (20631691762529 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148960262981 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨45, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (20631691762529 / 25000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148960262981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_46 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (16498554289897 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148962279653 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨46, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (16498554289897 / 20000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148962279653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_47 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41229399732497 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148964261029 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨47, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41229399732497 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148964261029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_48 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (3296994042697 / 4000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (11489662653 / 500000000000 : ℝ))
      (E := (cell12345 ⟨48, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (3296994042697 / 4000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (11489662653 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_49 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41195463113853 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148968262259 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨49, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41195463113853 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148968262259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_50 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82357024916911 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574485125509 / 25000000000000 : ℝ))
      (E := (cell12345 ⟨50, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82357024916911 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (574485125509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_51 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82323147106261 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148972260067 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨51, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82323147106261 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148972260067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_52 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82289292767119 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148974258843 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨52, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82289292767119 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148974258843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_53 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41127730935497 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297952551293 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨53, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41127730935497 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297952551293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_54 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82221654389537 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459591300063 / 20000000000000 : ℝ))
      (E := (cell12345 ⟨54, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82221654389537 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (459591300063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_55 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82187870294541 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148980269519 / 50000000000000 : ℝ))
      (E := (cell12345 ⟨55, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82187870294541 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (1148980269519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_56 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (4107705477897 / 5000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287245568297 / 12500000000000 : ℝ))
      (E := (cell12345 ⟨56, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (4107705477897 / 5000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287245568297 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_57 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (82120372151811 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297968519071 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨57, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (82120372151811 / 100000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297968519071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_58 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (41043329024183 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287246564099 / 12500000000000 : ℝ))
      (E := (cell12345 ⟨58, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (41043329024183 / 50000000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (287246564099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12345_59 : CellCertificate 12345 (28027561730457 / 312500000000000 : ℝ) (170146839194329 / 100000000000000000 : ℝ) (34393150209293 / 1000000000000000 : ℝ)
    (cell12345 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · norm_num [cell12345]
  · have h := gap_lower (n := 12345) (a := (2051324180499 / 2500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297976523933 / 100000000000000 : ℝ))
      (E := (cell12345 ⟨59, by decide⟩).energy) (xi := (34393150209293 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12345 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12345]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12345])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12345) (a := (2051324180499 / 2500000000000 : ℝ)) (b := (166913103047 / 100000000000000 : ℝ)) (q := (2297976523933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12345])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12345]

theorem cert12346_40 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (16539419466347 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297760676883 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨40, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (16539419466347 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297760676883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_41 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82662983523069 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459552934229 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨41, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82662983523069 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459552934229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_42 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82628893478437 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297768657823 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨42, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82628893478437 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297768657823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_43 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82594827167873 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148886318329 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨43, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82594827167873 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148886318329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_44 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41280392280781 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148888332991 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨44, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41280392280781 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148888332991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_45 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82526765629839 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287222578439 / 12500000000000 : ℝ))
      (E := (cell12346 ⟨45, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82526765629839 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287222578439 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_46 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20623192585797 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574446159493 / 25000000000000 : ℝ))
      (E := (cell12346 ⟨46, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20623192585797 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574446159493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_47 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20614699668061 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (91911545497 / 4000000000000 : ℝ))
      (E := (cell12346 ⟨47, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20614699668061 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (91911545497 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_48 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82424850587789 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574448156131 / 25000000000000 : ℝ))
      (E := (cell12346 ⟨48, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82424850587789 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (574448156131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_49 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (5149432878797 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287224582079 / 12500000000000 : ℝ))
      (E := (cell12346 ⟨49, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (5149432878797 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (287224582079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_50 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82357025062207 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297800614147 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨50, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82357025062207 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297800614147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_51 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (5145196722711 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (45956092259 / 2000000000000 : ℝ))
      (E := (cell12346 ⟨51, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (5145196722711 / 6250000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (45956092259 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_52 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (10286161691953 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148904325453 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨52, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (10286161691953 / 12500000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148904325453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_53 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (4112773147523 / 5000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297812607633 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨53, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (4112773147523 / 5000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297812607633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_54 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (16444331155907 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148908328779 / 50000000000000 : ℝ))
      (E := (cell12346 ⟨54, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (16444331155907 / 20000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (1148908328779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_55 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20546967998661 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459564124157 / 20000000000000 : ℝ))
      (E := (cell12346 ⟨55, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20546967998661 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (459564124157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_56 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41077055783861 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297824612373 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨56, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41077055783861 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297824612373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_57 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (20530093617711 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297828629133 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨57, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (20530093617711 / 25000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297828629133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_58 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (41043330338113 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297832608531 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨58, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (41043330338113 / 50000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297832608531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12346_59 : CellCertificate 12346 (112106559445163 / 1250000000000000 : ℝ) (1701330529975351 / 1000000000000000000 : ℝ) (171951457216009 / 5000000000000000 : ℝ)
    (cell12346 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · norm_num [cell12346]
  · have h := gap_lower (n := 12346) (a := (82052970156221 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297836606053 / 100000000000000 : ℝ))
      (E := (cell12346 ⟨59, by decide⟩).energy) (xi := (171951457216009 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12346 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12346]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12346])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12346) (a := (82052970156221 / 100000000000000 : ℝ)) (b := (33379881263 / 20000000000000 : ℝ)) (q := (2297836606053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12346])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12346]

theorem cert12347_40 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16539418867199 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (7180065129 / 312500000000 : ℝ))
      (E := (cell12347 ⟨40, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16539418867199 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (7180065129 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_41 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (1653259616869 / 2000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459524961823 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨41, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (1653259616869 / 2000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459524961823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_42 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82628891114501 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148814414419 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨42, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82628891114501 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148814414419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_43 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (5162176569949 / 6250000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148816420739 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨43, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (5162176569949 / 6250000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148816420739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_44 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (20640195706921 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (14360230291 / 625000000000 : ℝ))
      (E := (cell12347 ⟨44, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (20640195706921 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (14360230291 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_45 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (2578961381573 / 3125000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297640843389 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨45, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (2578961381573 / 3125000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297640843389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_46 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (41246384618813 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574411207763 / 25000000000000 : ℝ))
      (E := (cell12347 ⟨46, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (41246384618813 / 50000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574411207763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_47 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (8245879788019 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297648808417 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨47, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (8245879788019 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297648808417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_48 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82424850108809 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297652833039 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨48, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82424850108809 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297652833039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_49 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16478185178883 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (91906271423 / 4000000000000 : ℝ))
      (E := (cell12347 ⟨49, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16478185178883 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (91906271423 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_50 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82357025208081 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148830420511 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨50, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82357025208081 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148830420511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_51 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82323148021031 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459532964123 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨51, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82323148021031 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459532964123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_52 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (8228929430463 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297668781073 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨52, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (8228929430463 / 10000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297668781073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_53 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (20563866007597 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297672778997 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨53, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (20563866007597 / 25000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297672778997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_54 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82221657169957 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574419202957 / 25000000000000 : ℝ))
      (E := (cell12347 ⟨54, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82221657169957 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574419202957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_55 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82187873695133 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (229768081773 / 10000000000000 : ℝ))
      (E := (cell12347 ⟨55, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82187873695133 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (229768081773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_56 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (1643082271557 / 2000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459536958731 / 20000000000000 : ℝ))
      (E := (cell12347 ⟨56, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (1643082271557 / 2000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (459536958731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_57 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16424075358037 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148844397727 / 50000000000000 : ℝ))
      (E := (cell12347 ⟨57, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16424075358037 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (1148844397727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_58 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (16417332660871 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297692819729 / 100000000000000 : ℝ))
      (E := (cell12347 ⟨58, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (16417332660871 / 20000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (2297692819729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12347_59 : CellCertificate 12347 (896822980348999 / 10000000000000000 : ℝ) (425298172586553 / 250000000000000000 : ℝ) (85968582907777 / 2500000000000000 : ℝ)
    (cell12347 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · norm_num [cell12347]
  · have h := gap_lower (n := 12347) (a := (82052973092713 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574424200929 / 25000000000000 : ℝ))
      (E := (cell12347 ⟨59, by decide⟩).energy) (xi := (85968582907777 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12347 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12347]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12347])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12347) (a := (82052973092713 / 100000000000000 : ℝ)) (b := (83442855929 / 50000000000000 : ℝ)) (q := (574424200929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12347])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12347]

theorem cert12348_40 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41348545670613 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287185132607 / 12500000000000 : ℝ))
      (E := (cell12348 ⟨40, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41348545670613 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287185132607 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_41 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82662978164761 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148742530533 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨41, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82662978164761 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148742530533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_42 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82628888751457 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148744527581 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨42, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82628888751457 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148744527581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_43 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82594823071347 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297493042889 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨43, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82594823071347 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297493042889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_44 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41280390547309 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143593567661 / 6250000000000 : ℝ))
      (E := (cell12348 ⟨44, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41280390547309 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143593567661 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_45 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41263381395803 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148750527969 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨45, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41263381395803 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148750527969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_46 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82492768132799 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143594067481 / 6250000000000 : ℝ))
      (E := (cell12348 ⟨46, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82492768132799 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (143594067481 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_47 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82458797088831 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148754517519 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨47, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82458797088831 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148754517519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_48 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41212424815243 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287189129793 / 12500000000000 : ℝ))
      (E := (cell12348 ⟨48, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41212424815243 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (287189129793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_49 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (16478185145739 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148758514599 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨49, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (16478185145739 / 20000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148758514599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_50 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41178512677267 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (35898766637 / 1562500000000 : ℝ))
      (E := (cell12348 ⟨50, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41178512677267 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (35898766637 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_51 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41161574239613 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297525084163 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨51, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41161574239613 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297525084163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_52 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41144647537069 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (114876451309 / 5000000000000 : ℝ))
      (E := (cell12348 ⟨52, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41144647537069 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (114876451309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_53 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82255465110779 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297533065387 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨53, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82255465110779 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297533065387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_54 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82221658560803 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297537022169 / 100000000000000 : ℝ))
      (E := (cell12348 ⟨54, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82221658560803 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (2297537022169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_55 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41093937698003 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (229754107081 / 10000000000000 : ℝ))
      (E := (cell12348 ⟨55, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41093937698003 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (229754107081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_56 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (20538528897081 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148772515567 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨56, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (20538528897081 / 25000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148772515567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_57 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (41060189554917 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574387269287 / 25000000000000 : ℝ))
      (E := (cell12348 ⟨57, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (41060189554917 / 50000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (574387269287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_58 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82086665932753 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459510605623 / 20000000000000 : ℝ))
      (E := (cell12348 ⟨58, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82086665932753 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (459510605623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12348_59 : CellCertificate 12348 (896793489736583 / 10000000000000000 : ℝ) (850527436525221 / 500000000000000000 : ℝ) (42980719211101 / 1250000000000000 : ℝ)
    (cell12348 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · norm_num [cell12348]
  · have h := gap_lower (n := 12348) (a := (82052976029437 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148778528883 / 50000000000000 : ℝ))
      (E := (cell12348 ⟨59, by decide⟩).energy) (xi := (42980719211101 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12348 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12348]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12348])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12348) (a := (82052976029437 / 100000000000000 : ℝ)) (b := (83436009837 / 50000000000000 : ℝ)) (q := (1148778528883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12348])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12348]

theorem cert12349_40 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41348544173713 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287167674291 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨40, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41348544173713 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287167674291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_41 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (20665743871751 / 25000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297345368261 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨41, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (20665743871751 / 25000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297345368261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_42 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (10328610798663 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459469879111 / 20000000000000 : ℝ))
      (E := (cell12349 ⟨42, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (10328610798663 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (459469879111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_43 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41297410512181 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287169169807 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨43, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41297410512181 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287169169807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_44 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (16512155872473 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574339343507 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨44, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (16512155872473 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574339343507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_45 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (1650535227473 / 2000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297361382817 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨45, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (1650535227473 / 2000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297361382817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_46 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (16498553405741 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297365383907 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨46, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (16498553405741 / 20000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297365383907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_47 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82458796298167 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574342344041 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨47, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82458796298167 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574342344041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_48 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82424849152819 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148686679121 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨48, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82424849152819 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148686679121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_49 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82390925563593 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297377387499 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨49, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82390925563593 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297377387499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_50 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41178512750783 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297381344333 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨50, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41178512750783 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297381344333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_51 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82323148937961 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297385344621 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨51, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82323148937961 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297385344621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_52 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (41144647922073 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297389386227 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨52, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (41144647922073 / 50000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297389386227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_53 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (5140966636977 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297393348767 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨53, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (5140966636977 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297393348767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_54 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (10277707494009 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287174668453 / 12500000000000 : ℝ))
      (E := (cell12349 ⟨54, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (10277707494009 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (287174668453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_55 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (5136742318579 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (91896055201 / 4000000000000 : ℝ))
      (E := (cell12349 ⟨55, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (5136742318579 / 6250000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (91896055201 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_56 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (10269264699893 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148702691951 / 50000000000000 : ℝ))
      (E := (cell12349 ⟨56, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (10269264699893 / 12500000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (1148702691951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_57 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82120381429791 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297409355991 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨57, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82120381429791 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297409355991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_58 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82086668561421 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297413351961 / 100000000000000 : ℝ))
      (E := (cell12349 ⟨58, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82086668561421 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (2297413351961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

theorem cert12349_59 : CellCertificate 12349 (56047750232683 / 625000000000000 : ℝ) (340183415616523 / 200000000000000000 : ℝ) (13752687224149 / 400000000000000 : ℝ)
    (cell12349 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · norm_num [cell12349]
  · have h := gap_lower (n := 12349) (a := (82052978966391 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574354342051 / 25000000000000 : ℝ))
      (E := (cell12349 ⟨59, by decide⟩).energy) (xi := (13752687224149 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12349 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12349]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12349])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12349) (a := (82052978966391 / 100000000000000 : ℝ)) (b := (166858329763 / 100000000000000 : ℝ)) (q := (574354342051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12349])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12349]

end BstLean.Part263
