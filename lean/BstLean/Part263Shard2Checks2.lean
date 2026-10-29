import BstLean.Part263Shard2Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12275_40 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20674328131877 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307873176173 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨40, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20674328131877 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307873176173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_41 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20665794043247 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307877172439 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨41, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20665794043247 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307877172439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_42 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20657265903429 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307881167437 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨42, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20657265903429 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307881167437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_43 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82594974819669 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461577032207 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨43, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82594974819669 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461577032207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_44 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (3302436390439 / 4000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153944576441 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨44, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (3302436390439 / 4000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153944576441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_45 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82526868407913 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307893142409 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨45, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82526868407913 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307893142409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_46 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82492850730911 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307897128827 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨46, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82492850730911 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307897128827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_47 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (1649177134011 / 2000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576975292499 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨47, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (1649177134011 / 2000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576975292499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_48 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (16484977257511 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153952573491 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨48, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (16484977257511 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153952573491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_49 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (205977348657 / 250000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230790911719 / 10000000000000 : ℝ))
      (E := (cell12275 ⟨49, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (205977348657 / 250000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230790911719 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_50 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20589254049327 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307913137903 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨50, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20589254049327 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307913137903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_51 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20580779115561 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153958574181 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨51, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20580779115561 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153958574181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_52 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (2057231005723 / 2500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307921146483 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨52, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (2057231005723 / 2500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307921146483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_53 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (10281923433599 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307925129971 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨53, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (10281923433599 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307925129971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_54 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82221558153459 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307929096319 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨54, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82221558153459 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307929096319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_55 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41093876127331 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461586620373 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨55, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41093876127331 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461586620373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_56 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (16430793948857 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307937084669 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨56, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (16430793948857 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307937084669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_57 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82120210594351 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307941100697 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨57, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82120210594351 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307941100697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_58 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (1282601168391 / 1562500000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (288493135943 / 12500000000000 : ℝ))
      (E := (cell12275 ⟨58, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (1282601168391 / 1562500000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (288493135943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_59 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (2564148820769 / 3125000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307949100803 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨59, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (2564148820769 / 3125000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307949100803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12276_40 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (661578475697 / 800000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307728075779 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨40, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (661578475697 / 800000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307728075779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_41 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41331586713273 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461546408103 / 20000000000000 : ℝ))
      (E := (cell12276 ⟨41, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41331586713273 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461546408103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_42 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41314530592887 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (46154721269 / 2000000000000 : ℝ))
      (E := (cell12276 ⟨42, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41314530592887 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (46154721269 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_43 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16518994541957 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (92309601079 / 4000000000000 : ℝ))
      (E := (cell12276 ⟨43, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16518994541957 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (92309601079 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_44 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (82560907968709 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307744048263 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨44, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (82560907968709 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307744048263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_45 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (3301074677313 / 4000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576937002293 / 25000000000000 : ℝ))
      (E := (cell12276 ⟨45, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (3301074677313 / 4000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576937002293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_46 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16498569914513 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230775202653 / 10000000000000 : ℝ))
      (E := (cell12276 ⟨46, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16498569914513 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230775202653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_47 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41229427929253 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307756040533 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨47, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41229427929253 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307756040533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_48 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (2575777680043 / 3125000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153880024979 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨48, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (2575777680043 / 3125000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153880024979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_49 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (82390939252051 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153881997223 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨49, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (82390939252051 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153881997223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_50 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (82357016301553 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288470998769 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨50, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (82357016301553 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288470998769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_51 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (10290389610131 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153886017639 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨51, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (10290389610131 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153886017639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_52 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (1645784819237 / 2000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576944002459 / 25000000000000 : ℝ))
      (E := (cell12276 ⟨52, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (1645784819237 / 2000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576944002459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_53 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16451077703083 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (57694500737 / 2500000000000 : ℝ))
      (E := (cell12276 ⟨53, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16451077703083 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (57694500737 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_54 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41110779756671 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (115389201637 / 5000000000000 : ℝ))
      (E := (cell12276 ⟨54, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41110779756671 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (115389201637 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_55 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41093876963687 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461557603379 / 20000000000000 : ℝ))
      (E := (cell12276 ⟨55, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41093876963687 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461557603379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_56 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16430794345879 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461558395803 / 20000000000000 : ℝ))
      (E := (cell12276 ⟨56, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16430794345879 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461558395803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_57 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20530053222857 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307795975067 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨57, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20530053222857 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307795975067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_58 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (2052161934641 / 2500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307800001769 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨58, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (2052161934641 / 2500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307800001769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_59 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20513191296083 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307803996487 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨59, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20513191296083 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307803996487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12277_40 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41348653198867 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (288447878809 / 12500000000000 : ℝ))
      (E := (cell12277 ⟨40, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41348653198867 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (288447878809 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_41 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16532634136211 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (230758702247 / 10000000000000 : ℝ))
      (E := (cell12277 ⟨41, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16532634136211 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (230758702247 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_42 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41314529379371 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (57689775367 / 2500000000000 : ℝ))
      (E := (cell12277 ⟨42, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41314529379371 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (57689775367 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_43 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (20648742650193 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307595006971 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨43, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (20648742650193 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307595006971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_44 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41280453088637 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307598998991 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨44, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41280453088637 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307598998991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_45 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (8252686545853 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307602990167 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨45, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (8252686545853 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307602990167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_46 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (8249284841497 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576901744927 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨46, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (8249284841497 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576901744927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_47 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41229427508587 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307610966609 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨47, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41229427508587 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307610966609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_48 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (82424885235871 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461523001707 / 20000000000000 : ℝ))
      (E := (cell12277 ⟨48, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (82424885235871 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461523001707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_49 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (5149433690121 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153809493143 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨49, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (5149433690121 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153809493143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_50 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10294627050799 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307622957073 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨50, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10294627050799 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307622957073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_51 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10290389662551 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307626977989 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨51, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10290389662551 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307626977989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_52 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (1285769401489 / 1562500000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153815494017 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨52, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (1285769401489 / 1562500000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153815494017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_53 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41127694781257 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (144227186557 / 6250000000000 : ℝ))
      (E := (cell12277 ⟨53, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41127694781257 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (144227186557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_54 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41110780436831 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153819483057 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨54, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41110780436831 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153819483057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_55 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (20546938900121 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (92305719519 / 4000000000000 : ℝ))
      (E := (cell12277 ⟨55, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (20546938900121 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (92305719519 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_56 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (82153973714863 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307646988557 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨56, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (82153973714863 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307646988557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_57 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (3284808607553 / 4000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307650964719 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨57, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (3284808607553 / 4000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307650964719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_58 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16417295998907 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153827486119 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨58, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16417295998907 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153827486119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_59 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41026384052149 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576914737119 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨59, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41026384052149 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576914737119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12278_40 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82697303334333 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307438098959 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨40, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82697303334333 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307438098959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_41 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (20665791984129 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307442059579 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨41, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (20665791984129 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307442059579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_42 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41314528166311 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (57686151997 / 2500000000000 : ℝ))
      (E := (cell12278 ⟨42, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41314528166311 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (57686151997 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_43 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (8259496849263 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307450042251 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨43, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (8259496849263 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307450042251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_44 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82560904386671 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288431757983 / 12500000000000 : ℝ))
      (E := (cell12278 ⟨44, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82560904386671 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288431757983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_45 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41263431992513 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153729013287 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨45, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41263431992513 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153729013287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_46 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82492847258127 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307462047209 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨46, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82492847258127 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307462047209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_47 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (16491770835311 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307466065963 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨47, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (16491770835311 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307466065963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_48 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41212442355519 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153735011359 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨48, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41212442355519 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153735011359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_49 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41195469416227 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153737016897 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨49, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41195469416227 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153737016897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_50 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (3294280660473 / 4000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461495607733 / 20000000000000 : ℝ))
      (E := (cell12278 ⟨50, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (3294280660473 / 4000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461495607733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_51 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41161558860161 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (115374101773 / 5000000000000 : ℝ))
      (E := (cell12278 ⟨51, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41161558860161 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (115374101773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_52 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82289242429257 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153743011047 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨52, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82289242429257 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153743011047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_53 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82255390610089 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307489996269 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨53, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82255390610089 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307489996269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_54 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82221562234419 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230749401451 / 10000000000000 : ℝ))
      (E := (cell12278 ⟨54, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82221562234419 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230749401451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_55 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (8218775727399 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230749801511 / 10000000000000 : ℝ))
      (E := (cell12278 ⟨55, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (8218775727399 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230749801511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_56 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82153975700689 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461500399027 / 20000000000000 : ℝ))
      (E := (cell12278 ⟨56, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82153975700689 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461500399027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_57 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (4106010874327 / 5000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307506010551 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨57, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (4106010874327 / 5000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307506010551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_58 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (8208648260371 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (46150199979 / 2000000000000 : ℝ))
      (E := (cell12278 ⟨58, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (8208648260371 / 10000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (46150199979 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_59 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (16410554204901 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576878503981 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨59, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (16410554204901 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576878503981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12279_40 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20674325067981 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288411652817 / 12500000000000 : ℝ))
      (E := (cell12279 ⟨40, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20674325067981 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288411652817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_41 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82663165192927 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307297210571 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨41, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82663165192927 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307297210571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_42 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82629053907413 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307301200299 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨42, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82629053907413 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307301200299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_43 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (1032437079817 / 1250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576826297897 / 25000000000000 : ℝ))
      (E := (cell12279 ⟨43, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (1032437079817 / 1250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576826297897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_44 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82560902596899 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461461836817 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨44, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82560902596899 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461461836817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_45 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41263431256157 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461462635443 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨45, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41263431256157 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461462635443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_46 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20623211525509 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153658585093 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨46, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20623211525509 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153658585093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_47 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82458853336647 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230732116199 / 10000000000000 : ℝ))
      (E := (cell12279 ⟨47, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82458853336647 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230732116199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_48 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41212442093439 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307325151399 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨48, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41212442093439 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307325151399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_49 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (16478187724721 / 20000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (144208074743 / 6250000000000 : ℝ))
      (E := (cell12279 ⟨49, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (16478187724721 / 20000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (144208074743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_50 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20589254154463 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307333175991 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨50, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20589254154463 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307333175991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_51 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (8232311814079 / 10000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288417143591 / 12500000000000 : ℝ))
      (E := (cell12279 ⟨51, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (8232311814079 / 10000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288417143591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_52 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20572310790933 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153670585501 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨52, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20572310790933 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153670585501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_53 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82255391658139 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576836295393 / 25000000000000 : ℝ))
      (E := (cell12279 ⟨53, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82255391658139 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576836295393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_54 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82221563595611 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307349177931 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨54, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82221563595611 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307349177931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_55 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41093879473947 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153676578677 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨55, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41093879473947 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153676578677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_56 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82153977686873 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288419646999 / 12500000000000 : ℝ))
      (E := (cell12279 ⟨56, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82153977686873 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288419646999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_57 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41060109892287 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307361171669 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨57, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41060109892287 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307361171669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_58 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41043242606583 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153682570517 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨58, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41043242606583 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153682570517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_59 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (10256596743119 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307369139681 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨59, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (10256596743119 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307369139681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12280_40 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (16539459442101 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461429680241 / 20000000000000 : ℝ))
      (E := (cell12280 ⟨40, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (16539459442101 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461429680241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_41 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82663162450289 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307152416719 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨41, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82663162450289 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307152416719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_42 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41314525741557 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307156375939 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨42, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41314525741557 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307156375939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_43 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (1032437053487 / 1250000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576790099053 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨43, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (1032437053487 / 1250000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576790099053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_44 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41280450403979 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461432883691 / 20000000000000 : ℝ))
      (E := (cell12280 ⟨44, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41280450403979 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461432883691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_45 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82526861040393 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230716838327 / 10000000000000 : ℝ))
      (E := (cell12280 ⟨45, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82526861040393 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230716838327 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_46 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82492844946697 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307172407487 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨46, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82492844946697 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307172407487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_47 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20614713124363 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576794093107 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨47, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20614713124363 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576794093107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_48 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (8242488366339 / 10000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307180394579 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨48, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (8242488366339 / 10000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307180394579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_49 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20597734603847 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153592177369 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨49, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20597734603847 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153592177369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_50 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (10294627090559 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307188369053 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨50, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (10294627090559 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307188369053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_51 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82323118561811 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (57679809419 / 2500000000000 : ℝ))
      (E := (cell12280 ⟨51, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82323118561811 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (57679809419 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_52 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41144621949361 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307196375773 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨52, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41144621949361 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307196375773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_53 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (10281924088333 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (144200022737 / 6250000000000 : ℝ))
      (E := (cell12280 ⟨53, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (10281924088333 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (144200022737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_54 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (2055539123931 / 2500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307204338307 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨54, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (2055539123931 / 2500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307204338307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_55 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41093880311097 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307208355653 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨55, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41093880311097 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307208355653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_56 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41076989836707 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153606176943 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨56, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41076989836707 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153606176943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_57 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82120222082927 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (288402041233 / 12500000000000 : ℝ))
      (E := (cell12280 ⟨57, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82120222082927 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (288402041233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_58 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82086487822901 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576805084841 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨58, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82086487822901 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576805084841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_59 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82052776865641 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307224378897 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨59, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82052776865641 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307224378897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12281_40 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20674323537519 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288375461709 / 12500000000000 : ℝ))
      (E := (cell12281 ⟨40, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20674323537519 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288375461709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_41 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82663159708601 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (92280307121 / 4000000000000 : ℝ))
      (E := (cell12281 ⟨41, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82663159708601 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (92280307121 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_42 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41314524529863 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307011665553 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨42, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41314524529863 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307011665553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_43 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (8259496217343 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153507857449 / 50000000000000 : ℝ))
      (E := (cell12281 ⟨43, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (8259496217343 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153507857449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_44 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (10320112377481 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144188731761 / 6250000000000 : ℝ))
      (E := (cell12281 ⟨44, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (10320112377481 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144188731761 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_45 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82526859569263 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576755925891 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨45, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82526859569263 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576755925891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_46 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20623210948027 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307027700269 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨46, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20623210948027 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307027700269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_47 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (10307356457371 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (3604737027 / 156250000000 : ℝ))
      (E := (cell12281 ⟨47, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (10307356457371 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (3604737027 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_48 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41212441570287 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288379461671 / 12500000000000 : ℝ))
      (E := (cell12281 ⟨48, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41212441570287 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288379461671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_49 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20597734551951 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576759921773 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨49, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20597734551951 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576759921773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_50 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16471403366337 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307043676791 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨50, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16471403366337 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307043676791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_51 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82323118983387 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144190478787 / 6250000000000 : ℝ))
      (E := (cell12281 ⟨51, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82323118983387 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144190478787 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_52 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82289244634227 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288381454551 / 12500000000000 : ℝ))
      (E := (cell12281 ⟨52, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82289244634227 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288381454551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_53 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16451078751133 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307055660951 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨53, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16451078751133 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307055660951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_54 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16444313263861 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288382459093 / 12500000000000 : ℝ))
      (E := (cell12281 ⟨54, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16444313263861 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288382459093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_55 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20546940574223 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461412733813 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨55, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20546940574223 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461412733813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_56 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41076990830157 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307067646981 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨56, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41076990830157 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307067646981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_57 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82120224381599 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576767915613 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨57, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82120224381599 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576767915613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_58 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16417298086583 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (230707565307 / 10000000000000 : ℝ))
      (E := (cell12281 ⟨58, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16417298086583 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (230707565307 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_59 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (8205277978657 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307079615273 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨59, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (8205277978657 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2307079615273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12282_40 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82697291090637 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (72089346873 / 3125000000000 : ℝ))
      (E := (cell12282 ⟨40, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82697291090637 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (72089346873 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_41 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82663156967863 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306863053217 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨41, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82663156967863 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306863053217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_42 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82629046637247 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153433534571 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨42, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82629046637247 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153433534571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_43 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82594960068771 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306871088871 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨43, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82594960068771 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306871088871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_44 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (10320112154071 / 12500000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (36044922707 / 1562500000000 : ℝ))
      (E := (cell12282 ⟨44, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (10320112154071 / 12500000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (36044922707 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_45 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82526858098923 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306879079273 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨45, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82526858098923 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306879079273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_46 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82492842638271 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230688304853 / 10000000000000 : ℝ))
      (E := (cell12282 ⟨46, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82492842638271 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230688304853 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_47 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (20614712705299 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153443509403 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨47, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (20614712705299 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153443509403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_48 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (8242488261843 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153445523883 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨48, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (8242488261843 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153445523883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_49 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (20597734500213 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306895016203 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨49, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (20597734500213 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306895016203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_50 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (8235701693949 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153449520133 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨50, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (8235701693949 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153449520133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_51 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (20580779851379 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306903059189 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨51, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (20580779851379 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306903059189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_52 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (16457849074049 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288363376487 / 12500000000000 : ℝ))
      (E := (cell12282 ⟨52, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (16457849074049 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288363376487 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_53 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (4112769740257 / 5000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306911014039 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨53, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (4112769740257 / 5000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306911014039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_54 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (16444313536361 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (115345750207 / 5000000000000 : ℝ))
      (E := (cell12282 ⟨54, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (16444313536361 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (115345750207 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_55 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (16437552794397 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461383807707 / 20000000000000 : ℝ))
      (E := (cell12282 ⟨55, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (16437552794397 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461383807707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_56 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (8215398364757 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576730749049 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨56, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (8215398364757 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576730749049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_57 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82120226680589 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306926992119 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨57, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82120226680589 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306926992119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_58 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82086493043209 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306931023023 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨58, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82086493043209 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306931023023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_59 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (4102639135387 / 5000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306935026263 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨59, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (4102639135387 / 5000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306935026263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12283_40 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82697288032187 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153357251297 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨40, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82697288032187 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153357251297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_41 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41331577114037 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (23067185423 / 1000000000000 : ℝ))
      (E := (cell12283 ⟨41, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41331577114037 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (23067185423 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_42 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41314522107839 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306722527957 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨42, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41314522107839 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306722527957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_43 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82594957964981 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461345303627 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨43, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82594957964981 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461345303627 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_44 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41280447723059 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (92269220499 / 4000000000000 : ℝ))
      (E := (cell12283 ⟨44, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41280447723059 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (92269220499 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_45 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41263428314687 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153367255201 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨45, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41263428314687 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153367255201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_46 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (644475324103 / 781250000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153369255561 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨46, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (644475324103 / 781250000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153369255561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_47 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41229424992067 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (115337125681 / 5000000000000 : ℝ))
      (E := (cell12283 ⟨47, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41229424992067 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (115337125681 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_48 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82424882096957 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306746516669 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨48, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82424882096957 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306746516669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_49 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82390937794533 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153375229953 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨49, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82390937794533 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153375229953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_50 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82357017047889 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306754459481 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨50, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82357017047889 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306754459481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_51 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41161559914099 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (18454067637 / 800000000000 : ℝ))
      (E := (cell12283 ⟨51, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41161559914099 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (18454067637 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_52 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41144623053389 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306762502239 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨52, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41144623053389 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306762502239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_53 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (8225539585509 / 10000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306766482069 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨53, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (8225539585509 / 10000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306766482069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_54 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (4111078452237 / 5000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153385225283 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨54, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (4111078452237 / 5000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153385225283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_55 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (3287510625899 / 4000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (36043351001 / 1562500000000 : ℝ))
      (E := (cell12283 ⟨55, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (3287510625899 / 4000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (36043351001 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_56 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (5134624102199 / 6250000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288347307577 / 12500000000000 : ℝ))
      (E := (cell12283 ⟨56, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (5134624102199 / 6250000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288347307577 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_57 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82120228979897 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153391218539 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨57, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82120228979897 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153391218539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_58 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41043247826891 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153393224613 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨58, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41043247826891 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153393224613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_59 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (1641055712583 / 2000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461358086883 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨59, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (1641055712583 / 2000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461358086883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12284_40 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82697284974727 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153285038879 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨40, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82697284974727 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153285038879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_41 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16532630297847 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461314805563 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨41, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16532630297847 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461314805563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_42 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82629041795019 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153289020999 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨42, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82629041795019 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153289020999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_43 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82594955862061 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288322757683 / 12500000000000 : ℝ))
      (E := (cell12284 ⟨43, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82594955862061 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288322757683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_44 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41280446830249 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (144161626691 / 6250000000000 : ℝ))
      (E := (cell12284 ⟨44, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41280446830249 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (144161626691 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_45 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16505371032123 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576647513943 / 25000000000000 : ℝ))
      (E := (cell12284 ⟨45, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16505371032123 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576647513943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_46 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (5155802520803 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576648507299 / 25000000000000 : ℝ))
      (E := (cell12284 ⟨46, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (5155802520803 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576648507299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_47 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (10307356143473 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306598005111 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨47, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (10307356143473 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306598005111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_48 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20606220394039 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306602041183 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨48, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20606220394039 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306602041183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_49 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16478187517769 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153303009101 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨49, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16478187517769 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153303009101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_50 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (1029462714461 / 1250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (18452879947 / 800000000000 : ℝ))
      (E := (cell12284 ⟨50, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (1029462714461 / 1250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (18452879947 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_51 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82323120251433 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153307011897 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨51, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82323120251433 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153307011897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_52 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (5143077927739 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153308994731 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨52, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (5143077927739 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153308994731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_53 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16451079381103 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306622006031 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨53, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16451079381103 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306622006031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_54 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82221570408111 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153313006011 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨54, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82221570408111 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153313006011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_55 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41093883661681 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306630004709 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨55, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41093883661681 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306630004709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_56 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16430797524631 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153316990579 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨56, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16430797524631 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153316990579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_57 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82120231279523 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (144164874833 / 6250000000000 : ℝ))
      (E := (cell12284 ⟨57, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82120231279523 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (144164874833 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_58 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16417299652927 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306641990807 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨58, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16417299652927 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306641990807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_59 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (205131971377 / 250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153323008593 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨59, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (205131971377 / 250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153323008593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12285_40 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (16539456383651 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461285129863 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨40, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (16539456383651 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461285129863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_41 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (16532629750269 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306429685949 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨41, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (16532629750269 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306429685949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_42 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82629039375269 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306433670017 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨42, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82629039375269 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306433670017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_43 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82594953760011 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576609415021 / 25000000000000 : ℝ))
      (E := (cell12285 ⟨43, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82594953760011 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576609415021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_44 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82560891875707 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (144152603487 / 6250000000000 : ℝ))
      (E := (cell12285 ⟨44, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82560891875707 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (144152603487 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_45 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (16505370738529 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306445656563 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨45, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (16505370738529 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306445656563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_46 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41246419590631 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2883062077 / 125000000000 : ℝ))
      (E := (cell12285 ⟨46, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41246419590631 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2883062077 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_47 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (5153678019509 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306453611021 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨47, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (5153678019509 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306453611021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_48 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (3296995242241 / 4000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230645762131 / 10000000000000 : ℝ))
      (E := (cell12285 ⟨48, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (3296995242241 / 4000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230645762131 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_49 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82390937383789 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153230816087 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨49, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82390937383789 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153230816087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_50 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82357017266463 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306465641951 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨50, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82357017266463 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306465641951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_51 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82323120675221 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306469648767 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨51, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82323120675221 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306469648767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_52 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (10286155947673 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306473591541 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨52, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (10286155947673 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306473591541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_53 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41127698978207 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461295528987 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨53, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41127698978207 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461295528987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_54 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41110785885959 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (72077550921 / 3125000000000 : ℝ))
      (E := (cell12285 ⟨54, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41110785885959 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (72077550921 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_55 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (20546942249911 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153242800707 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨55, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (20546942249911 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153242800707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_56 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82153989611483 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153244808453 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨56, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82153989611483 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153244808453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_57 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82120233579467 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461298722753 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨57, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82120233579467 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461298722753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_58 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41043250437883 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (14415609929 / 625000000000 : ℝ))
      (E := (cell12285 ⟨58, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41043250437883 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (14415609929 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_59 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82052791472691 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306501597117 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨59, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82052791472691 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306501597117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12286_40 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82697278862773 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576570333669 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨40, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82697278862773 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576570333669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_41 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20665786503601 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (57657133513 / 2500000000000 : ℝ))
      (E := (cell12286 ⟨41, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20665786503601 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (57657133513 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_42 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82629036956427 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306289353267 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨42, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82629036956427 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306289353267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_43 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82594951658829 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306293313999 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨43, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82594951658829 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306293313999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_44 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41280445045873 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153148669943 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨44, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41280445045873 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153148669943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_45 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (16505370445093 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306301312777 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨45, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (16505370445093 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306301312777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_46 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41246419015213 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306305349493 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨46, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41246419015213 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306305349493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_47 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41229423738607 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288288666419 / 12500000000000 : ℝ))
      (E := (cell12286 ⟨47, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41229423738607 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288288666419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_48 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41212440268283 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153156657973 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨48, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41212440268283 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153156657973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_49 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20597734294841 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153158650913 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨49, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20597734294841 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153158650913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_50 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41178508688319 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (230632128733 / 10000000000000 : ℝ))
      (E := (cell12286 ⟨50, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41178508688319 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (230632128733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_51 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41161560549781 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306325329547 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨51, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41161560549781 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306325329547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_52 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82289248319457 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306329308479 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨52, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82289248319457 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306329308479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_53 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82255399007787 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461266656153 / 20000000000000 : ℝ))
      (E := (cell12286 ⟨53, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82255399007787 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461266656153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_54 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82221573136159 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306337302923 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨54, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82221573136159 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306337302923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_55 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41093885338161 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306341313241 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨55, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41093885338161 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306341313241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_56 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10269248950021 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115317265439 / 5000000000000 : ℝ))
      (E := (cell12286 ⟨56, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10269248950021 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115317265439 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_57 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82120235879729 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306349286393 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨57, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82120235879729 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306349286393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_58 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10260812935897 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461270660371 / 20000000000000 : ℝ))
      (E := (cell12286 ⟨58, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10260812935897 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461270660371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_59 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82052794394821 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306357292519 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨59, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82052794394821 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306357292519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12287_40 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82697275808279 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576534283461 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨40, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82697275808279 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576534283461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_41 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82663143278411 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461228221797 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨41, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82663143278411 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461228221797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_42 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41314517269247 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461229018349 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨42, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41314517269247 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461229018349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_43 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20648737389629 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306149081983 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨43, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20648737389629 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306149081983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_44 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82560888308613 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (115307653967 / 5000000000000 : ℝ))
      (E := (cell12287 ⟨44, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82560888308613 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (115307653967 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_45 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (3301074030363 / 4000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461231416647 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨45, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (3301074030363 / 4000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461231416647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_46 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82492836880339 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (288270136609 / 12500000000000 : ℝ))
      (E := (cell12287 ⟨46, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82492836880339 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (288270136609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_47 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16491769328599 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153082553617 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨47, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16491769328599 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153082553617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_48 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82424880017777 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576542266549 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨48, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82424880017777 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576542266549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_49 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (8239093697557 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153086543037 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨49, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (8239093697557 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153086543037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_50 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20589254371851 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461235421267 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨50, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20589254371851 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461235421267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_51 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16464624304891 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153090533067 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨51, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16464624304891 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153090533067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_52 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82289249058043 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306185081289 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨52, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82289249058043 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306185081289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_53 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41127700029817 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306189090551 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨53, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41127700029817 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306189090551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_54 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41110787250417 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (144137068213 / 6250000000000 : ℝ))
      (E := (cell12287 ⟨54, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41110787250417 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (144137068213 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_55 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20546943088349 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306197081129 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨55, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20546943088349 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306197081129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_56 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (8215399358921 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306201056779 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨56, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (8215399358921 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306201056779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_57 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82120238180309 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461241014863 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨57, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82120238180309 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461241014863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_58 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16417301219773 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306209071323 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨58, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16417301219773 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306209071323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_59 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82052797317191 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306213044237 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨59, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82052797317191 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306213044237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12288_40 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (20674318188693 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461198597623 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨40, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (20674318188693 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461198597623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_41 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41331570271683 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305996932617 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨41, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41331570271683 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305996932617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_42 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (8262903212147 / 10000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306000944207 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨42, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (8262903212147 / 10000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306000944207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_43 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (40329564189 / 48828125000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306004964039 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨43, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (40329564189 / 48828125000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306004964039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_44 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (8256088652631 / 10000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306008932951 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨44, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (8256088652631 / 10000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306008932951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_45 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41263424646737 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115300648397 / 5000000000000 : ℝ))
      (E := (cell12288 ⟨45, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41263424646737 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115300648397 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_46 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41246417865501 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1153008475293 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨46, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41246417865501 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1153008475293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_47 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (16491769161897 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306020938669 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨47, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (16491769161897 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306020938669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_48 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82424879499659 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306024930957 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨48, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82424879499659 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306024930957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_49 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (10298867096551 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306028926003 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨49, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (10298867096551 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306028926003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_50 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41178508799381 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306032922143 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨50, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41178508799381 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306032922143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_51 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (823231219499 / 1000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461207383499 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨51, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (823231219499 / 1000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461207383499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_52 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41144624898571 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306040909971 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨52, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41144624898571 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306040909971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_53 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41127700555977 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (144127806079 / 6250000000000 : ℝ))
      (E := (cell12288 ⟨53, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41127700555977 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (144127806079 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_54 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (16444315173189 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576512233973 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨54, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (16444315173189 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576512233973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_55 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (16437554806173 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306052905083 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨55, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (16437554806173 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306052905083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_56 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82153995578607 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230605691999 / 10000000000000 : ℝ))
      (E := (cell12288 ⟨56, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82153995578607 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230605691999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_57 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41060120240603 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306060918429 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨57, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41060120240603 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2306060918429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_58 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82086508710833 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461212979409 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨58, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82086508710833 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461212979409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_59 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82052800239801 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1153034455713 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨59, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82052800239801 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1153034455713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12289_40 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41348634851127 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305848897489 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨40, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41348634851127 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305848897489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_41 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82663137809269 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152926435073 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨41, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82663137809269 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152926435073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_42 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82629029705353 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (36029014229 / 1562500000000 : ℝ))
      (E := (cell12289 ⟨42, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82629029705353 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (36029014229 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_43 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (5162184085031 / 6250000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (144116306337 / 6250000000000 : ℝ))
      (E := (cell12289 ⟨43, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (5162184085031 / 6250000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (144116306337 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_44 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16512176948967 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92234596029 / 4000000000000 : ℝ))
      (E := (cell12289 ⟨44, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16512176948967 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92234596029 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_45 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82526847828661 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (9223475397 / 400000000000 : ℝ))
      (E := (cell12289 ⟨45, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82526847828661 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (9223475397 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_46 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16498566916483 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230587286379 / 10000000000000 : ℝ))
      (E := (cell12289 ⟨46, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16498566916483 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230587286379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_47 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16491768995337 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305876884529 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨47, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16491768995337 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305876884529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_48 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (8242487898221 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152940425669 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨48, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (8242487898221 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152940425669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_49 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (659127492559 / 800000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152942440267 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨49, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (659127492559 / 800000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152942440267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_50 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (10294627213839 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152944426319 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨50, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (10294627213839 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152944426319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_51 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82323122375897 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305892824667 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨51, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82323122375897 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305892824667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_52 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41144625268377 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576474213379 / 25000000000000 : ℝ))
      (E := (cell12289 ⟨52, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41144625268377 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576474213379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_53 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (20563850541187 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152950409463 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨53, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (20563850541187 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152950409463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_54 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82221577231489 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115295241819 / 5000000000000 : ℝ))
      (E := (cell12289 ⟨54, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82221577231489 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115295241819 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_55 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82187775708729 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305908844161 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨55, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82187775708729 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305908844161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_56 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82153997568361 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230591283933 / 10000000000000 : ℝ))
      (E := (cell12289 ⟨56, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82153997568361 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230591283933 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_57 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (4106012139121 / 5000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305916818737 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨57, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (4106012139121 / 5000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305916818737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_58 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41043255661539 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576480209539 / 25000000000000 : ℝ))
      (E := (cell12289 ⟨58, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41043255661539 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576480209539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_59 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (1641056063253 / 2000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288240604367 / 12500000000000 : ℝ))
      (E := (cell12289 ⟨59, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (1641056063253 / 2000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288240604367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12290_40 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82697266650723 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (92228196827 / 4000000000000 : ℝ))
      (E := (cell12290 ⟨40, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82697266650723 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (92228196827 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_41 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82663135076119 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152854431423 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨41, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82663135076119 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152854431423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_42 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (16525805458029 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461142574717 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨42, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (16525805458029 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461142574717 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_43 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82594943262787 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461143378809 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨43, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82594943262787 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461143378809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_44 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (20640220741047 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305720865063 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨44, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (20640220741047 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305720865063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_45 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82526846364637 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305724903633 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨45, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82526846364637 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305724903633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_46 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (5155802089661 / 6250000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576432222833 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨46, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (5155802089661 / 6250000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576432222833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_47 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (16491768828919 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305732885943 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨47, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (16491768828919 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305732885943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_48 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (10303109808179 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288217110779 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨48, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (10303109808179 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288217110779 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_49 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41195468183987 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152870445373 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨49, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41195468183987 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152870445373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_50 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82357017823253 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305744838881 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨50, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82357017823253 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305744838881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_51 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41161561401223 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461149769323 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨51, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41161561401223 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461149769323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_52 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41144625638439 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288219106617 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨52, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41144625638439 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288219106617 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_53 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (2570481350563 / 3125000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152878427769 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨53, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (2570481350563 / 3125000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152878427769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_54 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (20555394649367 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461152170381 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨54, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (20555394649367 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461152170381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_55 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82187777386989 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461152967861 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨55, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82187777386989 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461152967861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_56 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82153999558471 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (5764422037 / 250000000000 : ℝ))
      (E := (cell12290 ⟨56, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82153999558471 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (5764422037 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_57 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82120245083951 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288221604293 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨57, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82120245083951 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288221604293 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_58 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41043256967801 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152888417761 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨58, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41043256967801 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152888417761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_59 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82052806085739 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152890407383 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨59, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82052806085739 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152890407383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12291_40 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82697263600179 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305560998967 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨40, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82697263600179 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305560998967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_41 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82663132343917 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152782484723 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨41, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82663132343917 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152782484723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_42 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82629024875843 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288196118813 / 12500000000000 : ℝ))
      (E := (cell12291 ⟨42, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82629024875843 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288196118813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_43 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82594941165947 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305572941997 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨43, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82594941165947 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305572941997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_44 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82560881184369 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576394235891 / 25000000000000 : ℝ))
      (E := (cell12291 ⟨44, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82560881184369 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576394235891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_45 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82526844901401 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152790477311 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨45, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82526844901401 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152790477311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_46 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41246416143743 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (72049530449 / 3125000000000 : ℝ))
      (E := (cell12291 ⟨46, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41246416143743 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (72049530449 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_47 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82458843313213 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576397235729 / 25000000000000 : ℝ))
      (E := (cell12291 ⟨47, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82458843313213 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576397235729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_48 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82424877949323 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305592917853 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨48, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82424877949323 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305592917853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_49 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41195468083351 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461119391329 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨49, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41195468083351 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461119391329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_50 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (160853550657 / 195312500000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461120187963 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨50, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (160853550657 / 195312500000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461120187963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_51 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82323123229547 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (3688967879 / 160000000000 : ℝ))
      (E := (cell12291 ⟨51, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82323123229547 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (3688967879 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_52 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (16457850403503 / 20000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305608908233 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨52, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (16457850403503 / 20000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305608908233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_53 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (20563851067939 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305612948093 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨53, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (20563851067939 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305612948093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_54 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82221579963881 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461123384687 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨54, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82221579963881 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461123384687 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_55 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82187779065643 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305620949577 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨55, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82187779065643 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305620949577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_56 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82154001548937 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576406226371 / 25000000000000 : ℝ))
      (E := (cell12291 ⟨56, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82154001548937 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576406226371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_57 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82120247385799 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305628906147 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨57, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82120247385799 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305628906147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_58 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (20521629137101 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305632948277 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨58, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (20521629137101 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305632948277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_59 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41026404504533 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305636910073 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨59, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41026404504533 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305636910073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12292_40 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41348630275311 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305417132367 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨40, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41348630275311 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305417132367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_41 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41331564806331 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305421131217 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨41, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41331564806331 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305421131217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_42 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82629022462449 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305425141411 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨42, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82629022462449 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305425141411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_43 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41297469534987 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305429104027 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨43, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41297469534987 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305429104027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_44 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41280439702689 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (230543313623 / 10000000000000 : ℝ))
      (E := (cell12292 ⟨44, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41280439702689 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (230543313623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_45 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41263421719477 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152718559931 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨45, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41263421719477 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152718559931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_46 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (10311603892643 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305441112897 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨46, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (10311603892643 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305441112897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_47 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82458842482541 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576361278579 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨47, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82458842482541 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576361278579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_48 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20606219358471 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576362280721 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨48, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20606219358471 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576362280721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_49 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82390935966061 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305453078229 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨49, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82390935966061 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305453078229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_50 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41178509025053 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152728548249 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨50, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41178509025053 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152728548249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_51 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82323123657199 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461092223383 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨51, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82323123657199 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461092223383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_52 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (10286156594833 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576366269599 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨52, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (10286156594833 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576366269599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_53 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (8225540532597 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305469096587 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨53, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (8225540532597 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305469096587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_54 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (10277697666341 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461094622001 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨54, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (10277697666341 / 12500000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461094622001 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_55 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82187780744693 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576369278979 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨55, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82187780744693 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576369278979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_56 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82154003539759 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305481111383 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨56, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82154003539759 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305481111383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_57 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20530062421991 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305485093251 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨57, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20530062421991 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305485093251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_58 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20521629790371 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152744529081 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨58, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20521629790371 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152744529081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_59 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82052811932633 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152746530851 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨59, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82052811932633 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152746530851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12293_40 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (20674314375513 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (115263668979 / 5000000000000 : ℝ))
      (E := (cell12293 ⟨40, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (20674314375513 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (115263668979 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_41 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82663126882353 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152638674081 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨41, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82663126882353 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152638674081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_42 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41314510024981 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461056277511 / 20000000000000 : ℝ))
      (E := (cell12293 ⟨42, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41314510024981 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461056277511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_43 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (20648734243717 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152642690067 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨43, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (20648734243717 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152642690067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_44 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41280438813607 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305289384263 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨44, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41280438813607 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305289384263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_45 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41263420988647 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305293340533 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨45, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41263420988647 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305293340533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_46 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (1649856599911 / 2000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305297365769 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨46, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (1649856599911 / 2000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305297365769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_47 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82458841652577 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (92212053651 / 4000000000000 : ℝ))
      (E := (cell12293 ⟨47, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82458841652577 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (92212053651 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_48 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41212438459557 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305305324643 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨48, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41212438459557 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305305324643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_49 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (1647818715321 / 2000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305309314417 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨49, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (1647818715321 / 2000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305309314417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_50 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82357018164419 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305313367873 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨50, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82357018164419 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305313367873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_51 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41161562042701 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305317365269 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨51, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41161562042701 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305317365269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_52 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (3291570140013 / 4000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152660681713 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨52, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (3291570140013 / 4000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152660681713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_53 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (5140962898791 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305325360037 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨53, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (5140962898791 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305325360037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_54 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (10277697837251 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305329352581 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨54, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (10277697837251 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305329352581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_55 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (10273472803017 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305333338327 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨55, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (10273472803017 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305333338327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_56 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (10269250691367 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576334328583 / 25000000000000 : ℝ))
      (E := (cell12293 ⟨56, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (10269250691367 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576334328583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_57 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41060125995223 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288167667069 / 12500000000000 : ℝ))
      (E := (cell12293 ⟨57, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41060125995223 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288167667069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_58 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82086521774841 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305345342567 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨58, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82086521774841 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305345342567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_59 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82052814856439 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305349328807 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨59, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82052814856439 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305349328807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12294_40 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20674313613617 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152564840953 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨40, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20674313613617 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152564840953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_41 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82663124152991 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305133679013 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨41, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82663124152991 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305133679013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_42 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82629017638381 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305137688941 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨42, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82629017638381 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305137688941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_43 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20648733720157 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305141652771 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨43, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20648733720157 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305141652771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_44 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82560875849877 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461029137533 / 20000000000000 : ℝ))
      (E := (cell12294 ⟨44, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82560875849877 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461029137533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_45 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82526840516421 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305149675463 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨45, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82526840516421 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305149675463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_46 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (16498565770141 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305153674137 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨46, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (16498565770141 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305153674137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_47 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82458840823321 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576289420667 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨47, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82458840823321 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576289420667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_48 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82424876405013 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152580820461 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨48, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82424876405013 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152580820461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_49 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20597733891667 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152582832607 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨49, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20597733891667 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152582832607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_50 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41178509139661 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305169636061 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨50, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41178509139661 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305169636061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_51 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20580781128539 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (7203667717 / 312500000000 : ℝ))
      (E := (cell12294 ⟨51, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20580781128539 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (7203667717 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_52 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82289254242497 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305177645349 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨52, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82289254242497 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305177645349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_53 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (16451081487163 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305181620419 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨53, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (16451081487163 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305181620419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_54 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41110792032861 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152592825583 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨54, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41110792032861 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152592825583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_55 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41093892051987 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305189616809 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨55, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41093892051987 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305189616809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_56 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82154007522469 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305193632501 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨56, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82154007522469 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305193632501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_57 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20530063573311 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305197636053 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨57, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20530063573311 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305197636053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_58 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20521631097119 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461040324821 / 20000000000000 : ℝ))
      (E := (cell12294 ⟨58, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20521631097119 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461040324821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_59 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82052817780483 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (28815070653 / 1250000000000 : ℝ))
      (E := (cell12294 ⟨59, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82052817780483 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (28815070653 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12295_40 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82697251407869 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304986098049 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨40, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82697251407869 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304986098049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_41 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (3306524856983 / 4000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152495032519 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨41, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (3306524856983 / 4000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152495032519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_42 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41314507613853 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (450194161 / 19531250000 : ℝ))
      (E := (cell12295 ⟨42, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41314507613853 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (450194161 / 19531250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_43 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (10324366598407 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288124762283 / 12500000000000 : ℝ))
      (E := (cell12295 ⟨43, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (10324366598407 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288124762283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_44 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82560874073367 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461000409287 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨44, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82560874073367 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461000409287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_45 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (5157927441021 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (72031439557 / 3125000000000 : ℝ))
      (E := (cell12295 ⟨45, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (5157927441021 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (72031439557 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_46 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82492827706607 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152505019001 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨46, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82492827706607 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152505019001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_47 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41229419997387 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (115250703981 / 5000000000000 : ℝ))
      (E := (cell12295 ⟨47, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41229419997387 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (115250703981 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_48 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (4121243794579 / 5000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152509035861 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨48, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (4121243794579 / 5000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152509035861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_49 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16478187073583 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305022071699 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨49, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16478187073583 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305022071699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_50 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41178509197407 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461005215577 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨50, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41178509197407 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461005215577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_51 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82323124943461 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576257507357 / 25000000000000 : ℝ))
      (E := (cell12295 ⟨51, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82323124943461 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576257507357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_52 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82289254985181 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305034042141 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨52, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82289254985181 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305034042141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_53 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41127704245723 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (230503805477 / 10000000000000 : ℝ))
      (E := (cell12295 ⟨53, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41127704245723 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (230503805477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_54 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82221585433869 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461008412959 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨54, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82221585433869 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461008412959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_55 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82187785784207 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152523005211 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨55, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82187785784207 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152523005211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_56 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82154009514357 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461010001361 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨56, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82154009514357 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461010001361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_57 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41060128298179 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (115252702543 / 5000000000000 : ℝ))
      (E := (cell12295 ⟨57, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41060128298179 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (115252702543 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_58 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82086527002389 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461011604207 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨58, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82086527002389 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (461011604207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_59 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41026410352383 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305062031999 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨59, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41026410352383 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2305062031999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12296_40 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82697248362257 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152421284653 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨40, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82697248362257 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152421284653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_41 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (16532623739421 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576211641243 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨41, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (16532623739421 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576211641243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_42 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41314506408969 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304850574941 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨42, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41314506408969 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304850574941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_43 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82594930694749 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304854540289 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨43, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82594930694749 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304854540289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_44 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (20640218074421 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304858519377 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨44, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (20640218074421 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304858519377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_45 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41263418798519 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304862511621 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨45, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41263418798519 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304862511621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_46 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (10311603320407 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460973303243 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨46, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (10311603320407 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460973303243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_47 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (16491767833387 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304870532137 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨47, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (16491767833387 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304870532137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_48 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (643944338897 / 781250000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152437249627 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨48, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (643944338897 / 781250000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152437249627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_49 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82390935169791 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304878533877 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨49, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82390935169791 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304878533877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_50 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82357018510897 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304882516523 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨50, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82357018510897 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304882516523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_51 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (20580781343329 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152443252101 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨51, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (20580781343329 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152443252101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_52 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (10286156966047 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304890494817 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨52, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (10286156966047 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304890494817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_53 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82255409547549 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304894486057 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨53, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82255409547549 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304894486057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_54 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82221586802449 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460979706887 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨54, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82221586802449 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460979706887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_55 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82187787464833 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230490251917 / 10000000000000 : ℝ))
      (E := (cell12296 ⟨55, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82187787464833 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230490251917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_56 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (410770057533 / 500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230490649633 / 10000000000000 : ℝ))
      (E := (cell12296 ⟨56, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (410770057533 / 500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230490649633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_57 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82120258899789 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576227630467 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨57, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82120258899789 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576227630467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_58 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82086529616579 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304914474231 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨58, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82086529616579 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304914474231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_59 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (10256602953661 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304918527239 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨59, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (10256602953661 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304918527239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12297_40 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (8269724531763 / 10000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (92187963827 / 4000000000000 : ℝ))
      (E := (cell12297 ⟨40, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (8269724531763 / 10000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (92187963827 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_41 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (4133155798529 / 5000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460940624017 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨41, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (4133155798529 / 5000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460940624017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_42 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (3305160416363 / 4000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460941420161 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨42, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (3305160416363 / 4000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460941420161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_43 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82594928603109 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576177774099 / 25000000000000 : ℝ))
      (E := (cell12297 ⟨43, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82594928603109 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576177774099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_44 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82560870522827 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304715106491 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨44, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82560870522827 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304715106491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_45 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41263418069263 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304719071677 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨45, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41263418069263 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304719071677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_46 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82492825420653 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152361554387 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨46, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82492825420653 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152361554387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_47 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82458838339803 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (144045443693 / 6250000000000 : ℝ))
      (E := (cell12297 ⟨47, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82458838339803 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (144045443693 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_48 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82424874866721 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304731100203 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨48, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82424874866721 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304731100203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_49 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82390934972297 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460947010349 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨49, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82390934972297 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460947010349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_50 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82357018627569 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152369534929 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨50, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82357018627569 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152369534929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_51 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41161562901861 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (900290271 / 39062500000 : ℝ))
      (E := (cell12297 ⟨51, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41161562901861 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (900290271 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_52 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82289256472083 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576186765591 / 25000000000000 : ℝ))
      (E := (cell12297 ⟨52, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82289256472083 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576186765591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_53 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20563852651031 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152375516151 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨53, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20563852651031 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152375516151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_54 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41110794085731 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460951012017 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨54, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41110794085731 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460951012017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_55 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82187789145853 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288094885499 / 12500000000000 : ℝ))
      (E := (cell12297 ⟨55, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82187789145853 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288094885499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_56 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41077006749599 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304763041993 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨56, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41077006749599 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304763041993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_57 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (16424052240707 / 20000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304767049077 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨57, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (16424052240707 / 20000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304767049077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_58 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41043266115523 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304771042821 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨58, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41043266115523 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304771042821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_59 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (1282075414907 / 1562500000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152387509827 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨59, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (1282075414907 / 1562500000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152387509827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12298_40 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (20674310568497 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304555735869 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨40, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (20674310568497 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304555735869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_41 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (16532622649 / 20000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152279865189 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨41, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (16532622649 / 20000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152279865189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_42 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41314504000559 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576140935167 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨42, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41314504000559 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576140935167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_43 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41297463256167 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152283853907 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨43, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41297463256167 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152283853907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_44 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (20640217187199 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152285845089 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨44, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (20640217187199 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152285845089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_45 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82526834680801 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304575687171 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨45, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82526834680801 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304575687171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_46 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82492824278797 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576144924497 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨46, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82492824278797 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576144924497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_47 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82458837513379 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152291860803 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨47, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82458837513379 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152291860803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_48 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82424874355293 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (72018365559 / 3125000000000 : ℝ))
      (E := (cell12298 ⟨48, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82424874355293 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (72018365559 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_49 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82390934775431 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304591684227 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨49, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82390934775431 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304591684227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_50 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82357018744831 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304595678951 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨50, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82357018744831 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304595678951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_51 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41161563117339 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152299840087 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨51, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41161563117339 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152299840087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_52 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (822892572163 / 1000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152301842899 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨52, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (822892572163 / 1000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152301842899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_53 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82255411661171 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230460769351 / 10000000000000 : ℝ))
      (E := (cell12298 ⟨53, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82255411661171 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230460769351 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_54 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (20555397385227 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460922340157 / 20000000000000 : ℝ))
      (E := (cell12298 ⟨54, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (20555397385227 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460922340157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_55 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82187790827267 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304615704891 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨55, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82187790827267 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304615704891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_56 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (1643080309843 / 2000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (14403873143 / 625000000000 : ℝ))
      (E := (cell12298 ⟨56, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (1643080309843 / 2000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (14403873143 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_57 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41060131753799 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304623691597 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨57, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41060131753799 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304623691597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_58 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82086534845789 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (14403922923 / 625000000000 : ℝ))
      (E := (cell12298 ⟨58, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82086534845789 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (14403922923 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_59 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41026414739523 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576157921677 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨59, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41026414739523 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576157921677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12299_40 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8269723923133 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304412431179 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨40, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8269723923133 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304412431179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_41 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41331555260183 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152208227291 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨41, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41331555260183 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152208227291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_42 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41314502797033 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (36006569309 / 1562500000000 : ℝ))
      (E := (cell12299 ⟨42, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41314502797033 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (36006569309 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_43 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (3303796976897 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152212216659 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨43, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (3303796976897 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152212216659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_44 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82560866975591 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304428388039 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨44, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82560866975591 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304428388039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_45 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41263416611931 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (72013513029 / 3125000000000 : ℝ))
      (E := (cell12299 ⟨45, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41263416611931 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (72013513029 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_46 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82492823137687 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304436401553 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨46, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82492823137687 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304436401553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_47 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41229418343831 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (230444039969 / 10000000000000 : ℝ))
      (E := (cell12299 ⟨47, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41229418343831 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (230444039969 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_48 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82424873844533 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304444410099 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨48, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82424873844533 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304444410099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_49 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82390934579193 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304448372403 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨49, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82390934579193 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304448372403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_50 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82357018862681 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460890480549 / 20000000000000 : ℝ))
      (E := (cell12299 ⟨50, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82357018862681 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460890480549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_51 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82323126666183 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304456381377 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨51, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82323126666183 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304456381377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_52 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (20572314490257 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152230182559 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨52, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (20572314490257 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152230182559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_53 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8225541271869 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304464410667 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨53, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8225541271869 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304464410667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_54 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41110795455393 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304468397499 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨54, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41110795455393 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304468397499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_55 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (3287511700363 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152236190933 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨55, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (3287511700363 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152236190933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_56 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41077008742729 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304476360823 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨56, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41077008742729 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304476360823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_57 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (10265033226497 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304480390321 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨57, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (10265033226497 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304480390321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_58 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8208653746081 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460896869761 / 20000000000000 : ℝ))
      (E := (cell12299 ⟨58, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8208653746081 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460896869761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_59 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41026416202141 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152244175469 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨59, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41026416202141 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152244175469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

end BstLean.Part263
